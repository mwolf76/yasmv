;; This file is part of the yasmv distribution
;; (c) 2011-2022 M. Pensallorto < marco DOT pensallorto AT gmail DOT com >
;;
;; A simple emacs major mode for yasmv input language, based on generic mode
;; see https://www.emacswiki.org/emacs/GenericMode
(require 'generic-x)

(define-generic-mode
    ;; name of the mode to create
    'smv-mode

  ;; comments start with '--'
  '("--")

  ;; keywords
  '(
    "DEFINE"
    "MODULE"
    "VAR"
    "INIT"
    "INVAR"
    "TRANS"

    "next"
    "case"
    "else"
    "end")

  ;; custom faces
  '(("?:" . 'font-lock-keyword-face)
    (":=" . 'font-lock-keyword-face)

    ("=" . 'font-lock-builtin-face)
    (">" . 'font-lock-builtin-face)
    (">=" . 'font-lock-builtin-face)
    ("<" . 'font-lock-builtin-face)
    ("<=" . 'font-lock-builtin-face)

    ;; logical ops
    ("->" . 'font-lock-builtin-face)
    ("&&" . 'font-lock-builtin-face)
    ("||" . 'font-lock-builtin-face)

    ("~" . 'font-lock-builtin-face)
    ("!" . 'font-lock-builtin-face)

    ;; arithmentical ops
    ("+" . 'font-lock-builtin-face)
    ("-" . 'font-lock-builtin-face)
    ("*" . 'font-lock-builtin-face)
    ("/" . 'font-lock-builtin-face)
    ("%" . 'font-lock-builtin-face)
    ("&" . 'font-lock-builtin-face)
    ("|" . 'font-lock-builtin-face)

    ;; constants
    ("FALSE" . 'font-lock-constant-face)
    ("TRUE" . 'font-lock-constant-face)

    ;; directives
    ;; FIXME: doesn't work with #word-width
    ("^#.*$" . 'font-lock-variable-name-face)

    ;; brackets and braces
    ("{" . 'font-lock-builtin-face)
    ("\\[" . 'font-lock-builtin-face)
    ("}" . 'font-lock-builtin-face)
    ("\\]" . 'font-lock-builtin-face)

    ;; ',', ':' and ';' are keywords
    ("," . 'font-lock-keyword-face)
    (":" . 'font-lock-keyword-face)
    (";" . 'font-lock-keyword-face)

    ("boolean"  . 'font-lock-type-face)
    ("u?int\d*" . 'font-lock-type-face)
    )

  ;; files for which to activate this mode
  '("\\.smv$")

  ;; other functions to call
  nil

  ;; doc string for this mode
  "A mode for yasmv smv files")
