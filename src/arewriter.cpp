
// Code started by editing tooling_sample.cpp from LLVM/Clang distribution,
// by Eli Bendersky (eliben@gmail.com), public domain

#include <sstream>
#include <string>
#include <unordered_set>

#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "llvm/Support/raw_ostream.h"

#include "dofunc.h"

using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;

static llvm::cl::OptionCategory MyToolCategory("Do-functions rewriter options");
static cl::opt<std::string> BitcodeFilename("bc", cl::init("R.bin.bc"), cl::desc("Filename of the bitcode file for R binary"), cl::value_desc("filename"),
  cl::cat(MyToolCategory));

static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);
static cl::extrahelp MoreHelp("\nThe tool rewrites the given C source files of GNU-R, changing (some)\ndo-functions to accept their arguments explicitly, instead of via a linked list.\n");

const bool DEBUG = false;
const bool DUMP = false;

typedef std::unordered_set<DeclRefExpr*> KnownAccessesTy;

class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
public:
  MyASTVisitor(Rewriter &R) : TheRewriter(R) {}

  std::string printLoc(SourceLocation l) {
    return l.printToString(TheRewriter.getSourceMgr());
  }

  Stmt* skipParen(Stmt *s) {
    if (ParenExpr *p = dyn_cast<ParenExpr>(s)) {
      return p->getSubExpr();
    }
    return s;
  }

  bool isListFieldAccess(Stmt*& stmt, FieldDecl *fd) {  // advances stmt
   
  //  `-ParenExpr 0x2b48120 <line:390:17, col:39> 'struct SEXPREC *' lvalue   <--------------------------------- the CAR starts here
  //    `-MemberExpr 0x2b480f0 <col:18, col:33> 'struct SEXPREC *' lvalue .carval 0x29115e0
  //      `-MemberExpr 0x2b480c0 <col:18, col:25> 'struct listsxp_struct':'struct listsxp_struct' lvalue .listsxp 0x2917db0
  //        `-MemberExpr 0x2b48090 <col:18, col:23> 'union (anonymous union at ../../src/include/Rinternals.h:267:5)':'union SEXPREC::(anonymous at ../../sr
  //          `-ImplicitCastExpr 0x2b48078 <col:18, col:20> 'struct SEXPREC *' <LValueToRValue>
  //            `-ParenExpr 0x2b48058 <col:18, col:20> 'struct SEXPREC *' lvalue
   
    Stmt *s = stmt;

    s = skipParen(s);
    if (MemberExpr *m = dyn_cast<MemberExpr>(s)) {

      if (!m->isLValue() || m->isArrow()) {
        return false;
      }
      if (m->getMemberDecl() != fd) {
        return false;
      }
      s = m->getBase();
    } else {
      return false;
    }
  
    s = skipParen(s);  
    if (MemberExpr *m = dyn_cast<MemberExpr>(s)) {

      if (!m->isLValue() || m->isArrow()) {
        return false;
      }

      if (m->getMemberDecl() != sexpRecListSxpFieldDecl) {
        return false;
      }
      s = m->getBase();
    } else {
      return false;
    }
  
    s = skipParen(s);
    if (MemberExpr *m = dyn_cast<MemberExpr>(s)) {
      if (!m->isLValue() || !m->isArrow()) {
        return false;
      }
      if (m->getMemberDecl() != sexpRecUnionFieldDecl) {
        return false;
      }
      s = m->getBase();
    } else {
      return false;
    }  

    s = skipParen(s);
    
    if (ImplicitCastExpr *ic = dyn_cast<ImplicitCastExpr>(s)) {
      s = ic->getSubExprAsWritten();
    }
    
    s = skipParen(s);
    stmt = s;  
    return true;
  }
  
  // detect list accesses of form CA<ncars>R(CD<ncdrs>R(var))
  //   where ncars > 0 || ncdrs > 0
  
  bool isListAccess(Stmt *s, unsigned& ncars, unsigned& ncdrs, VarDecl*& var, SourceLocation& loc) {

      // declaration references (nodes) of already detected list accesses
      // this is used to avoid multiple detection for the same complex access, e.g.
      //   with CADR(x), we don't want to detect also CDR(x)

    unsigned _ncars = 0;
    while (isListFieldAccess(s, listSxpCarFieldDecl)) {
      _ncars++;
    }
      
    unsigned _ncdrs = 0;
    while (isListFieldAccess(s, listSxpCdrFieldDecl)) {
      _ncdrs++;
    }

    if (_ncars > 0 || _ncdrs > 0) {
      if (DeclRefExpr *d = dyn_cast<DeclRefExpr>(s)) {
        if (VarDecl *v = dyn_cast<VarDecl>(d->getDecl())) {

          auto dsearch = knownAccesses.find(d);
          if (dsearch == knownAccesses.end()) {
          
            knownAccesses.insert(d);
        
            ncars = _ncars;
            ncdrs = _ncdrs;
            var = v;
            loc = d->getLocStart();
    
            return true;
          }
        }
      }
    }

    return false;
  }
  
  bool isListAccess(Stmt *s, ListAccess& la) {

    unsigned ncars, ncdrs;
    VarDecl* var;
    SourceLocation loc;

    if (!isListAccess(s, ncars, ncdrs, var, loc)) {
      return false;
    }
    
    if (ncars != 1) {  // ListAccess only supports CADnR accesses
      return false;
    }
    
    la.varName = var->getNameAsString();
    la.isArgsVar = (var == argsDecl);
    la.line = TheRewriter.getSourceMgr().getExpansionLineNumber(loc);
    la.ncdrs = ncdrs;
    
    return true;
  }

  bool VisitStmt(Stmt *s) {
  
    if (BinaryOperator *bo = dyn_cast<BinaryOperator>(s)) {
      if (bo->isAssignmentOp()) {
        if (DeclRefExpr *dr = dyn_cast<DeclRefExpr>(bo->getLHS())) {
          if (dr->getDecl() == argsDecl) {
            if (DEBUG) llvm::errs() << "Modification of args variable at " << printLoc(bo->getOperatorLoc()) << "\n";
          }
        }
      }
    }
    
    if (0) {
      unsigned ncars, ncdrs;
      VarDecl *var;
      SourceLocation loc;

      if (isListAccess(s, ncars, ncdrs, var, loc)) {
        llvm::errs() << "List access to variable \"" << cast<VarDecl>(var)->getNameAsString() << "\" ncars=" << std::to_string(ncars) << " ncdrs=" << 
          std::to_string(ncdrs) << " at " << printLoc(s->getLocStart()) << "\n";
      }
    }
    
    ListAccess la;
    if (isListAccess(s, la)) {
      llvm::errs() << "Detected list access " << la.str() << "\n";
    }
   
    return true;
  }

  bool VisitDecl(Decl *d) {

    // load declarations needed to parse list accesses
    // NOTE: child nodes are visited after the parent nodes of the AST tree
    
    if (FieldDecl *fd = dyn_cast<FieldDecl>(d)) {

      if (fd->getNameAsString() == "listsxp" && fd->getParent()->isUnion() && fd->getParent()->getNameAsString() == "") {
        RecordDecl *ud = fd->getParent();
       
        if (RecordDecl *up = dyn_cast<RecordDecl>(ud->getParent())) {
          if (up == sexpRecDecl && isa<ElaboratedType>(fd->getType())) {

            const ElaboratedType *et = dyn_cast<ElaboratedType>(fd->getType());
          
            if (const RecordType *rt = dyn_cast<RecordType>(et->getNamedType().getTypePtr())) {
              if (rt->getDecl() == listSxpDecl) {

                sexpRecUnionDecl = ud;
                if (DEBUG) llvm::errs() << "Detected declaration of anonymous SEXPREC union.\n";        
        
       
                sexpRecListSxpFieldDecl = fd;
                if (DEBUG) llvm::errs() << "Detected listsxp field in SEXPREC.\n"; 
              }
            }
          }
        }
      }
      
      // NOTE: not checking type of fields
      if (fd->getNameAsString() == "carval" && fd->getParent() == listSxpDecl) {
        listSxpCarFieldDecl = fd;
        if (DEBUG) llvm::errs() << "Detected car field in listsxp.\n";
      }

      if (fd->getNameAsString() == "cdrval" && fd->getParent() == listSxpDecl) {
        listSxpCdrFieldDecl = fd;
        if (DEBUG) llvm::errs() << "Detected cdr field in listsxp.\n";
      }

      if (fd->getNameAsString() == "tagval" && fd->getParent() == listSxpDecl) {
        listSxpTagFieldDecl = fd;
        if (DEBUG) llvm::errs() << "Detected tag field in listsxp.\n";
      }
      
      if (fd->getNameAsString() == "u" && fd->getParent() == sexpRecDecl) {
        sexpRecUnionFieldDecl = fd;
        if (DEBUG) llvm::errs() << "Detected u field (union) in SEXPREC.\n";
      }
    }

    if (RecordDecl *rd = dyn_cast<RecordDecl>(d)) {
    
      if (rd->getParentFunctionOrMethod() == NULL && rd->isCompleteDefinition() && rd->getLexicalParent()->isTranslationUnit() &&
        rd->getNameAsString() == "SEXPREC" && rd->isStruct()) {
        
        sexpRecDecl = rd;
        if (DEBUG) llvm::errs() << "Detected declaration of SEXPREC.\n";
        return true;
      }

      if (rd->getParentFunctionOrMethod() == NULL && rd->isCompleteDefinition() && rd->getLexicalParent()->isTranslationUnit() &&
        rd->getNameAsString() == "listsxp_struct" && rd->isStruct()) {
        
        listSxpDecl = rd;
        if (DEBUG) llvm::errs() << "Detected declaration of listsxp_struct.\n";
        return true;
      }      
    }
  
    if (!inDoFunction) {
      return true;
    }

    // Detect shadowing of the args argument by a local variable
    // FIXME: this can possibly be removed
    if (isa<VarDecl>(d) && !isa<ParmVarDecl>(d)) {
      if (cast<VarDecl>(d)->getNameAsString() == argsDecl->getNameAsString()) {
        llvm::errs() << "Declaration of local variable \"" << cast<VarDecl>(d)->getNameAsString() << "\" which shadows function argument in function \"" << funName << "\"\n";
        inDoFunction = false;
        return true;
      }
    }
    
    return true;
  }

  bool VisitFunctionDecl(FunctionDecl *f) {

    // Only function definitions (with bodies), not declarations.
    if (!f->hasBody()) {
     inDoFunction = false;
     return true;
    }
    
    Stmt *FuncBody = f->getBody();

    // TODO: perhaps easier to simply check by function name

    unsigned nparams = f->param_size();
    if (nparams != 4) {
     inDoFunction = false;
     return true;
    }

    funName = f->getNameInfo().getName().getAsString();
    std::string dopref = "do_";
    if (funName.substr(0, dopref.length()) != dopref) {
     inDoFunction = false;
     return true;
    }
    
    for(unsigned i = 0; i < nparams; i++) {
      ParmVarDecl *p = f->getParamDecl(i);
      QualType t = p->getTypeSourceInfo()->getType();
      if (t.getAsString() != "SEXP") {
        inDoFunction = false;
        return true;
      }
    }

    argsDecl = f->getParamDecl(2);
    llvm::errs() << "Function " << funName << " may be a do_XXX function with args argument \"" << argsDecl->getNameAsString() << "\".\n";
    inDoFunction = true;
    knownAccesses.clear();
    
    return true;
  }

private:
  Rewriter &TheRewriter;

  // RecordDecl 0x1a6b510 <../../src/include/Rinternals.h:220:1, line:224:1> line:220:8 struct listsxp_struct definition
  // |-FieldDecl 0x1a6b5e0 <line:221:5, col:21> col:21 carval 'struct SEXPREC *'
  // |-FieldDecl 0x1a6b650 <line:222:5, col:21> col:21 cdrval 'struct SEXPREC *'
  // `-FieldDecl 0x1a6b6c0 <line:223:5, col:21> col:21 tagval 'struct SEXPREC *
  RecordDecl *listSxpDecl = NULL;
  FieldDecl *listSxpCarFieldDecl = NULL;
  FieldDecl *listSxpCdrFieldDecl = NULL;
  FieldDecl *listSxpTagFieldDecl = NULL;

  // RecordDecl 0x1a6bd10 prev 0x1a6b280 <../../src/include/Rinternals.h:265:9, line:275:1> line:265:16 struct SEXPREC definition <======= sexpRecDecl
  // |-FieldDecl 0x1a6bde0 <line:259:5, col:27> col:27 sxpinfo 'struct sxpinfo_struct':'struct sxpinfo_struct'
  // |-FieldDecl 0x1a71a50 <line:260:5, col:21> col:21 attrib 'struct SEXPREC *'
  // |-FieldDecl 0x1a71ac0 <line:261:5, col:21> col:21 gengc_next_node 'struct SEXPREC *'
  // |-FieldDecl 0x1a71b30 <col:5, col:39> col:39 gengc_prev_node 'struct SEXPREC *'
  // |-RecordDecl 0x1a71b80 <line:267:5, line:274:5> line:267:5 union definition  <======================================== sexpRecUnionDecl
  // | |-FieldDecl 0x1a71c70 <line:268:2, col:24> col:24 primsxp 'struct primsxp_struct':'struct primsxp_struct'
  // | |-FieldDecl 0x1a71d10 <line:269:2, col:23> col:23 symsxp 'struct symsxp_struct':'struct symsxp_struct'
  // | |-FieldDecl 0x1a71db0 <line:270:2, col:24> col:24 listsxp 'struct listsxp_struct':'struct listsxp_struct'  <======== sexpRecListSxpFieldDecl
  // | |-FieldDecl 0x1a71e50 <line:271:2, col:23> col:23 envsxp 'struct envsxp_struct':'struct envsxp_struct'
  // | |-FieldDecl 0x1a71ef0 <line:272:2, col:23> col:23 closxp 'struct closxp_struct':'struct closxp_struct'
  // | `-FieldDecl 0x1a71f90 <line:273:2, col:24> col:24 promsxp 'struct promsxp_struct':'struct promsxp_struct'
  // `-FieldDecl 0x1a72070 <line:267:5, line:274:7> col:7 u 'union (anonymous union at ../../src/include/Rinternals.h:267:5)':'union SEXPREC::(anonymous at ../../src/include/Rintern
  //            <=== sexpRecUnionFieldDecl
  
  RecordDecl *sexpRecDecl = NULL;
  RecordDecl *sexpRecUnionDecl = NULL;
  FieldDecl *sexpRecListSxpFieldDecl = NULL;
  FieldDecl *sexpRecUnionFieldDecl = NULL;

  ParmVarDecl *argsDecl = NULL; // the "args" argument of the present do_XXX function
  std::string funName;
  
  bool inDoFunction; // FIXME: is this flag needed?
  
  KnownAccessesTy knownAccesses; // already known list accesses
  
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer(Rewriter &R) : Visitor(R) {}

  bool HandleTopLevelDecl(DeclGroupRef DR) override {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
      Visitor.TraverseDecl(*b);
      if (DUMP) (*b)->dump();
    }
    return true;
  }

/*  
   virtual void HandleTranslationUnit(clang::ASTContext &Context) {
     Visitor.TraverseDecl(Context.getTranslationUnitDecl());
   }
*/
private:
  MyASTVisitor Visitor;
};

// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public ASTFrontendAction {
public:
  MyFrontendAction() {}
  void EndSourceFileAction() override {
    SourceManager &SM = TheRewriter.getSourceMgr();
    llvm::errs() << "** EndSourceFileAction for: "
                 << SM.getFileEntryForID(SM.getMainFileID())->getName() << "\n";

    // Now emit the rewritten buffer.
    TheRewriter.getEditBuffer(SM.getMainFileID()).write(llvm::outs());
  }

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef file) override {
    llvm::errs() << "** Creating AST consumer for: " << file << "\n";
    llvm::errs() << "** bitcode file is " << BitcodeFilename.getValue() << "\n";
    TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<MyASTConsumer>(TheRewriter);
  }

private:
  Rewriter TheRewriter;
};

int main(int argc, const char **argv) {
  CommonOptionsParser op(argc, argv, MyToolCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  // ClangTool::run accepts a FrontendActionFactory, which is then used to
  // create new objects implementing the FrontendAction interface. Here we use
  // the helper newFrontendActionFactory to create a default factory that will
  // return a new MyFrontendAction object every time.
  // To further customize this, we could create our own factory class.
  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}
