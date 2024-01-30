(lang dune 2.9)
(name z3-cex)
(source (github ryosu-sato/z3-cex))
(authors "Sato, Ryosuke <rsato@acm.org>")
(maintainers "Sato, Ryosuke <rsato@acm.org>")

(package
 (name z3-cex)
 (version 1.0)
 (synopsis "Printing counterexample by z3")
 (depends
  (dune (>= 1.0.2))
  (batteries (>= 3.0.0))
  ocamlfind
  (smtlib-utils (>= 0.3.1))
  z3))

(generate_opam_files)
