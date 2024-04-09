/root/fiat-crypto//src/ExtractionOCaml/word_by_word_montgomery: wrong argument '0x'; option 'm' expects an integer expression.


USAGE: /root/fiat-crypto//src/ExtractionOCaml/word_by_word_montgomery [OPTS...] curve_description machine_wordsize m [function_to_synthesize...]


  --lang {C|Rust|Go|Java|JSON|Zig}           The output language code should be emitted in.  Defaults to C if no language is given.  Case-sensitive.
  --package-name                             The name of the package, for languages that support it.
  --class-name                               The name of the class, for languages that support it.
  --package-case                             The case convention for the default package name.  Only meaningful when the package name is inferred from curve_description, rather than given explicitly with --package-name.
                                             Valid options are: flat case (alternatively: flatcase), upper flat case (alternatively: UPPER FLAT CASE, UPPERFLATCASE), camelCase (alternatively: lower camelCase, lowerCamelCase, dromedaryCase), PascalCase (alternatively: UpperCamelCase, Upper Camel Case, StudlyCase), snake_case (alternatively: pothole_case), SCREAMING_SNAKE_CASE (alternatively: MACRO_CASE, CONSTANT_CASE), camel_Snake_Case, Pascal_Snake_Case, kebab-case (alternatively: dash-case, lisp-case), doner|case, TRAIN-CASE (alternatively: COBOL-CASE, SCREAMING-KEBAB-CASE), Train-Case (alternatively: HTTP-Header-Case).
                                             
  --class-case                               The case convention for the default class name.  Only meaningful when the class name is inferred from curve_description, rather than given explicitly with --class-name.
                                             Valid options are: flat case (alternatively: flatcase), upper flat case (alternatively: UPPER FLAT CASE, UPPERFLATCASE), camelCase (alternatively: lower camelCase, lowerCamelCase, dromedaryCase), PascalCase (alternatively: UpperCamelCase, Upper Camel Case, StudlyCase), snake_case (alternatively: pothole_case), SCREAMING_SNAKE_CASE (alternatively: MACRO_CASE, CONSTANT_CASE), camel_Snake_Case, Pascal_Snake_Case, kebab-case (alternatively: dash-case, lisp-case), doner|case, TRAIN-CASE (alternatively: COBOL-CASE, SCREAMING-KEBAB-CASE), Train-Case (alternatively: HTTP-Header-Case).
                                             
  --private-function-case                    The case convention for non-exported function names.  Default is to not adjust case, resulting in, roughly, snake_case.
                                             Valid options are: flat case (alternatively: flatcase), upper flat case (alternatively: UPPER FLAT CASE, UPPERFLATCASE), camelCase (alternatively: lower camelCase, lowerCamelCase, dromedaryCase), PascalCase (alternatively: UpperCamelCase, Upper Camel Case, StudlyCase), snake_case (alternatively: pothole_case), SCREAMING_SNAKE_CASE (alternatively: MACRO_CASE, CONSTANT_CASE), camel_Snake_Case, Pascal_Snake_Case, kebab-case (alternatively: dash-case, lisp-case), doner|case, TRAIN-CASE (alternatively: COBOL-CASE, SCREAMING-KEBAB-CASE), Train-Case (alternatively: HTTP-Header-Case).
                                             
  --public-function-case                     The case convention for exported function names.  Default is to not adjust case, resulting in, roughly, snake_case.
                                             Valid options are: flat case (alternatively: flatcase), upper flat case (alternatively: UPPER FLAT CASE, UPPERFLATCASE), camelCase (alternatively: lower camelCase, lowerCamelCase, dromedaryCase), PascalCase (alternatively: UpperCamelCase, Upper Camel Case, StudlyCase), snake_case (alternatively: pothole_case), SCREAMING_SNAKE_CASE (alternatively: MACRO_CASE, CONSTANT_CASE), camel_Snake_Case, Pascal_Snake_Case, kebab-case (alternatively: dash-case, lisp-case), doner|case, TRAIN-CASE (alternatively: COBOL-CASE, SCREAMING-KEBAB-CASE), Train-Case (alternatively: HTTP-Header-Case).
                                             
  --private-type-case                        The case convention for non-exported type names.  Default is to not adjust case, resulting in, roughly, snake_case.
                                             Valid options are: flat case (alternatively: flatcase), upper flat case (alternatively: UPPER FLAT CASE, UPPERFLATCASE), camelCase (alternatively: lower camelCase, lowerCamelCase, dromedaryCase), PascalCase (alternatively: UpperCamelCase, Upper Camel Case, StudlyCase), snake_case (alternatively: pothole_case), SCREAMING_SNAKE_CASE (alternatively: MACRO_CASE, CONSTANT_CASE), camel_Snake_Case, Pascal_Snake_Case, kebab-case (alternatively: dash-case, lisp-case), doner|case, TRAIN-CASE (alternatively: COBOL-CASE, SCREAMING-KEBAB-CASE), Train-Case (alternatively: HTTP-Header-Case).
                                             
  --public-type-case                         The case convention for exported type names.  Default is to not adjust case, resulting in, roughly, snake_case.
                                             Valid options are: flat case (alternatively: flatcase), upper flat case (alternatively: UPPER FLAT CASE, UPPERFLATCASE), camelCase (alternatively: lower camelCase, lowerCamelCase, dromedaryCase), PascalCase (alternatively: UpperCamelCase, Upper Camel Case, StudlyCase), snake_case (alternatively: pothole_case), SCREAMING_SNAKE_CASE (alternatively: MACRO_CASE, CONSTANT_CASE), camel_Snake_Case, Pascal_Snake_Case, kebab-case (alternatively: dash-case, lisp-case), doner|case, TRAIN-CASE (alternatively: COBOL-CASE, SCREAMING-KEBAB-CASE), Train-Case (alternatively: HTTP-Header-Case).
                                             
  --no-prefix-fiat                           Don't prefix functions with fiat_
  --static                                   Declare the functions as static, i.e., local to the file.
  --internal-static                          Declare internal functions as static, i.e., local to the file.
  --inline                                   Declare all functions as inline.
  --inline-internal                          Declare internal functions as inline.
  --no-wide-int                              Don't use integers wider than the bitwidth.
  --widen-carry                              Widen carry bit integer types to either the byte type, or to the full bitwidth if --widen-bytes is also passed.
  --widen-bytes                              Widen byte types to the full bitwidth.
  --no-select                                Use expressions that don't require cmov.
  --split-multiret                           Don't allow instructions to return two results. This should always be set for bedrock2.
  --use-value-barrier                        Guard some expressions with an assembly barrier to prevent compilers from generating non-constant-time code for cmovznz.
  --no-primitives                            Suppress the generation of the bodies of primitive operations such as addcarryx, subborrowx, cmovznz, mulx, etc.
  --no-field-element-typedefs                Do not use type aliases for field elements based on bounds, Montgomery-domain vs not Montgomery-domain, etc.
  --emit-all-casts                           Rather than performing language-specific cast-adjustment, just emit all casts that are present in the intermediate representation, annotating all constructions.
  --relax-primitive-carry-to-bitwidth        For any (comma-separated) bitwidths passed to this argument, use bitwidth-sized bounds rather than tighter bounds for the carry return value of primitives such as addcarryx and subborrowx.
  --cmovznz-by-mul                           Use an alternative implementation of cmovznz using multiplication rather than bitwise-and with -1.
  --shiftr-astatic void-uint1                       Astatic void uint1 types at the output of (>>) operations.
  --only-signed                              Only allow signed integer types.
  --hints-file                               An assembly file to be read for hinting the synthesis process.  Use - for stdin.  To check multiple files against the same synthesized operation(s), pass this argument multiple times.
  --output, -o                               The name of the file to write output to.  Use - for stdout.  (default: -)
  --output-asm                               The name of the file to write generated assembly to.  Use - for stdout.  (default: -)
  --asm-reg                                  A comma-separated list of registers to use for calling conventions.  Only relevant when --hints-file is specified.
                                             Defaults to the System V AMD64 ABI of rdi,rsi,rdx,rcx,r8,r9.  Note that registers are first used for outputs and then inputs.
                                             
  --asm-callee-saved-registers               Either 'System V AMD64' (indicating rbx,rsp,rbp,r12,r13,r14,r15), 'Microsoft x64' (indicating rbx,rbp,rdi,rsi,rsp,r12,r13,r14,r15), or a comma-separated list of registers which are callee-saved / non-volatile.  Only relevant when --hints-file is specified.
                                             Defaults to System V AMD64.
                                             
  --asm-stack-size                           The number of bytes of stack.  Only relevant when --hints-file is specified.  Defaults to 0 plus the maximum statically knowable increase to `rsp` (via `push`, `pop`, `sub`, `add`, and `lea` instructions) the code.
  --no-error-on-unused-asm-functions         Don't error if there are global labels in the hints-file which are not requested functions.
  --asm-input-first                          By default, output pointers are assumed to come before input arguments in the C code the assembly hints are based on.  This flag reverses that convention.
  --asm-reg-rtl                              By default, registers are assumed to be assigned to function arguments from left to right in the hints file.  This flag reverses that convention to be right-to-left.  Note that this flag interacts with --asm-input-first, which determines whether the output pointers are to the left or to the right of the input arguments.
  --asm-error-on-unique-name-mismatch        By default, when there's only one assembly function in a --hints-file and only one function requested to be synthesized, the name of the assembly function is ignored.  Passing this flag disables this behavior, raising an error if the names mismatch regardless of whether there are multiple functions or just one.
  --doc-text-before-function-name            Documentation Option: A custom string to insert before the function name in each docstring.  Default: The function 
  --doc-text-before-type-name                Documentation Option: A custom string to insert before the type name in each docstring.  Default: The type 
  --doc-newline-before-package-declaration   Documentation Option: For languages that emit package declarations, add an extra newline before the declaration.  Primarily useful to detach the header from the Go package.
  --doc-newline-in-typedef-bounds            Documentation Option: When emitting the documentation comment for typedefs, insert a newline between "Bounds:" and the bounds rather than a space.
  --doc-prepend-header-raw                   Documentation Option: Prepend a line before the documentation header at the top of the file.  This argument can be passed multiple times to insert multiple lines.
  --doc-prepend-header                       Documentation Option: Prepend a line at the beginning of the documentation header at the top of the file.  This argument can be passed multiple times to insert multiple lines.  Lines will be automatically commented.
  -h, --help                                 Display this list of options
  curve_description                          A string which will be prefixed to every function name generated
  machine_wordsize                           The machine bitwidth (e.g., 32 or 64)
  m                                          The prime (e.g., '2^434 - (2^216*3^137 - 1)')
  function_to_synthesize                     A space-separated list of functions that should be synthesized.  If no functions are given, all functions are synthesized.
                                             Valid options are mul, square, add, sub, opp, from_montgomery, to_montgomery, nonzero, selectznz, to_bytes, from_bytes, one, msat, divstep_precomp, divstep, sat_from_bytes, jumpdivstep_precomp, jumpdivstep_precomp_hd, inner_loop, inner_loop_hd, update_fg, update_vr.
                                             



