(lang dune 3.4)

(name lambda)

(generate_opam_files true)

(source
 (github tozarin/lambda))

(authors "Startsev Matvey")

(maintainers "https://github.com/Tozarin")

(license LGPL-3.0-only)

(package
 (name lambda)
 (synopsis "Lambda solver")
 (description "Lambda solver with small step")
 (depends
  ocaml
  dune
  angstrom
  (ppx_inline_test :with-test)
  qcheck-core
  ppx_expect
  ppx_show
  ppx_deriving
  (odoc :with-doc)
  (ocamlformat :build)
  base))
