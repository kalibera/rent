
// Code started by editing tooling_sample.cpp from LLVM/Clang distribution,
// by Eli Bendersky (eliben@gmail.com), public domain

#include <sstream>
#include <string>
#include <unordered_set>

#include <llvm/IR/Function.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>

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
#include "ftable.h"

using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;

static llvm::cl::OptionCategory MyToolCategory("Do-functions rewriter options");
static cl::opt<std::string> BitcodeFilename("bc", cl::init("R.bin.bc"), cl::desc("Filename of the bitcode file for R binary"), cl::value_desc("filename"),
  cl::cat(MyToolCategory));
static cl::opt<bool> VerboseOption("v", cl::init(false), cl::desc("Verbose output."), cl::value_desc("verbose"), cl::cat(MyToolCategory));

static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);
static cl::extrahelp MoreHelp("\nThe tool rewrites the given C source files of GNU-R, changing (some)\ndo-functions to accept their arguments explicitly, instead of via a linked list.\n");

const bool DEBUG = false;
const bool DUMP = false;

struct IRAnalyzer {

  llvm::LLVMContext context;
  FunctionTableTy funtab;
  llvm::Module *m;
  
  public:
    IRAnalyzer(std::string bcFName) {
      llvm::SMDiagnostic error;
      m = parseIRFile(bcFName, error, context).release();

      if (!m) {
        llvm::errs() << "ERROR: Cannot read IR file " << bcFName << "\n";
        error.print("arewriter", llvm::errs());
        exit(2);
      }
  
      if (!readFunctionTable(m, funtab)) {
        llvm::errs() << "Could not read function table.\n";
        exit(2);
      }
    }
    
    ~IRAnalyzer() {
      delete m;
    }
};

// get resolved list accesses for a simple do-function
//   returns false if the function is not a do function or is not simple
//   simple implies fixed number of arguments and all accesses resolved

bool getDoFunctionInfo(std::string funName, ResolvedListAccessesTy &listAccesses, unsigned &arity) {

  static IRAnalyzer ir(BitcodeFilename.getValue());

  llvm::Function *fun = ir.m->getFunction(funName);
  if (!fun) {
    if (DEBUG) llvm::errs() << "Cannot find function " << funName << " in module " << BitcodeFilename.getValue() << "\n";
    return false;
  }
  
  if (!isDoFunction(fun, ir.funtab)) {
    if (VerboseOption.getValue() || DEBUG) llvm::errs() << "Not analyzing function " << funName << " which is not a do_function\n";
    return false;
  }
  
  int a = maxArity(fun, ir.funtab);
  
  DoFunctionInfo nfo = analyzeDoFunction(fun);
  if (nfo.usesTags || nfo.computesArgsLength || nfo.complexUseOfArgs || 
    nfo.complexUseOfOp || nfo.complexUseOfCall || nfo.complexUseOfEnv /* FIXME: these could perhaps be allowed? */ ||
    !nfo.checkArityCalled || nfo.effectiveArity < 0 || a != nfo.effectiveArity) {
    
    if (VerboseOption.getValue() || DEBUG) llvm::errs() << "Not analyzing function " << funName << " which is not simple: " << nfo.str() << 
      " (nominal arity " << std::to_string(a) << ")\n";
    return false;
  }
  
  arity = a;
  listAccesses = nfo.listAccesses;
  if (VerboseOption.getValue()) llvm::errs() << "Analyzing function " << funName << "\n";
  return true;
}

typedef std::unordered_set<DeclRefExpr*> KnownAccessesTy;

class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
public:
  MyASTVisitor(Rewriter &r) : rewriter(r) {}

  std::string printLoc(SourceLocation l) {
    return l.printToString(rewriter.getSourceMgr());
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
    la.line = rewriter.getSourceMgr().getExpansionLineNumber(loc);
    la.ncdrs = ncdrs;
    
    return true;
  }

  bool VisitStmt(Stmt *s) {

    if (!inDoFunction) {
      return true;
    }
  
    if (BinaryOperator *bo = dyn_cast<BinaryOperator>(s)) {
      if (bo->isAssignmentOp()) {
        if (DeclRefExpr *dr = dyn_cast<DeclRefExpr>(bo->getLHS())) {
          if (dr->getDecl() == argsDecl) {
            if (DEBUG) llvm::errs() << "Modification of args variable at " << printLoc(bo->getOperatorLoc()) << "\n";
          }
        }
      }
    }
    
   /*
      unsigned ncars, ncdrs;
      VarDecl *var;
      SourceLocation loc;

      if (isListAccess(s, ncars, ncdrs, var, loc)) {
        llvm::errs() << "List access to variable \"" << cast<VarDecl>(var)->getNameAsString() << "\" ncars=" << std::to_string(ncars) << " ncdrs=" << 
          std::to_string(ncdrs) << " at " << printLoc(s->getLocStart()) << "\n";
      }
    */
    
    ListAccess la;
    if (isListAccess(s, la)) {
      llvm::errs() << "Detected list access " << la.str() << " in function " << funName << "\n";
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

    unsigned nparams = f->param_size();
    if (nparams != 4) {
      inDoFunction = false;
      return true;
    }

    // this check is not necessary as do_functions are detected at IR level
    for(unsigned i = 0; i < nparams; i++) {
      ParmVarDecl *p = f->getParamDecl(i);
      QualType t = p->getTypeSourceInfo()->getType();
      if (t.getAsString() != "SEXP") {
        inDoFunction = false;
        return true;
      }
    }

    ResolvedListAccessesTy listAccesses;
    unsigned arity;
    
    if (!getDoFunctionInfo(f->getNameAsString(), listAccesses, arity)) {
      inDoFunction = false;
      return true;
    }

    inDoFunction = true;
    funName = f->getNameAsString();
    argsDecl = f->getParamDecl(2);
    knownAccesses.clear();
    if (DEBUG) llvm::errs() << "Rewriting/analyzing simple function " << funName << "\n";
    
    if (arity > 0) {
    
      // rewrite declaration
      //   "SEXP args" -> "SEXP arg1, SEXP arg2, SEXP arg3"
    
      std::string decl;
      for(unsigned i = 0; i < arity; i++) { // starting with arg0
        decl += "SEXP arg" + std::to_string(i + 1);
        if (i < arity - 1) {
          decl += ", ";
        }
      }
      rewriter.ReplaceText(argsDecl->getSourceRange(), decl);

    } else {
    
      // removing the "args" argument
      // need to remove the extra comma (args separator)
      
      SourceLocation opTokenStartLoc = f->getParamDecl(1)->getLocEnd();
      SourceLocation commaAfterOpLoc = opTokenStartLoc.getLocWithOffset(rewriter.getRangeSize(SourceRange(opTokenStartLoc, opTokenStartLoc)));
      
      SourceLocation argsTokenStartLoc = f->getParamDecl(2)->getLocEnd();
      SourceLocation commaAfterArgsLoc = argsTokenStartLoc.getLocWithOffset(rewriter.getRangeSize(SourceRange(argsTokenStartLoc, argsTokenStartLoc)));      

      rewriter.ReplaceText(SourceRange(commaAfterOpLoc, commaAfterArgsLoc), ","); // we delete ", SEXP args,"
    }
    return true;
  }

private:
  Rewriter &rewriter;

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
  MyASTConsumer(Rewriter &r) : visitor(r) {}

  bool HandleTopLevelDecl(DeclGroupRef dr) override {
    for (DeclGroupRef::iterator di = dr.begin(), de = dr.end(); di != de; ++di) {
      visitor.TraverseDecl(*di);
      if (DUMP) (*di)->dump();
    }
    return true;
  }

/*  
   virtual void HandleTranslationUnit(clang::ASTContext &Context) {
     visitor.TraverseDecl(Context.getTranslationUnitDecl());
   }
*/
private:
  MyASTVisitor visitor;
};

// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public ASTFrontendAction {
public:
  MyFrontendAction() {}
  void EndSourceFileAction() override {
    SourceManager &sm = rewriter.getSourceMgr();
    llvm::errs() << "** EndSourceFileAction for: "
                 << sm.getFileEntryForID(sm.getMainFileID())->getName() << "\n";

    // Now emit the rewritten buffer.
    rewriter.getEditBuffer(sm.getMainFileID()).write(llvm::outs());
  }

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &ci,
                                                 StringRef file) override {
    llvm::errs() << "** Creating AST consumer for: " << file << "\n";
    llvm::errs() << "** Bitcode file is " << BitcodeFilename.getValue() << "\n";
    rewriter.setSourceMgr(ci.getSourceManager(), ci.getLangOpts());
    return llvm::make_unique<MyASTConsumer>(rewriter);
  }

private:
  Rewriter rewriter;
};

int main(int argc, const char **argv) {
  CommonOptionsParser op(argc, argv, MyToolCategory);
  ClangTool tool(op.getCompilations(), op.getSourcePathList());

  // ClangTool::run accepts a FrontendActionFactory, which is then used to
  // create new objects implementing the FrontendAction interface. Here we use
  // the helper newFrontendActionFactory to create a default factory that will
  // return a new MyFrontendAction object every time.
  // To further customize this, we could create our own factory class.
  return tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}
