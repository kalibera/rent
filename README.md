# rent

This project includes code for specific static analysis and rewriting of the
C source code of [GNU R](http://www.r-project.org/), the implementation of
the R language. The analysis focuses on VM entry points (sometimes also
known as `do_` functions). A `do_` function has a definition of the form

``
SEXP do_XXX(SEXP call, SEXP op, SEXP args, SEXP env);
``

where `call` is the AST of the call to the respective R entry point, `op` is
a runtime representation of it (an object of type `BUILTINSXP` or
`SPECIALSXP`), `args` is a single-linked list of arguments to the functions
(each argument has a name and a value), and `env` is an environment the R
entry point is being executed in. The objective of the static analysis in
this project is to find out how a `do_` function uses its arguments; it is
known and this work confirms that most of the `do_` functions use arguments
(`args`) and meta-arguments (`call`, `op`, `env`) in simple ways.

The rewriting part of this project rewrites the C source code of the `do_`
functions so that they accept their arguments directly on the C stack (not
in the linked list); this is only applicable to simple functions (no use of
names, fixed number of arguments, each access can be easily mapped to a
fixed argument), as discovered by the analysis. The rewriting can also
remove meta-arguments from `do_` functions that do not need them.

The tools are intended to be used semi-automatically, the resulting code has
to be verified manually and made prettier. The analysis works on the LLVM
bitcode for the R binary (see [rchk](http://www.github.com/kalibera/rchk)
for more details on how to get this bitcode). The rewriting works on the
CLANG AST level and uses the CLANG rewriter.
