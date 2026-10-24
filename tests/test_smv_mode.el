;;; test_smv_mode.el --- Tests for smv-mode  -*- lexical-binding: t; -*-

;; This file is part of the yasmv distribution
;; (c) 2026 M. Pensallorto < marco DOT pensallorto AT gmail DOT com >

;;; Commentary:

;; Run from the repository root:
;;
;;   emacs -Q --batch -l tools/smv-mode.el -l tests/test_smv_mode.el \
;;     -f ert-run-tests-batch-and-exit

;;; Code:

(require 'ert)
(require 'smv-mode)

(defconst smv-test--grammar
  (expand-file-name "../src/parser/grammars/smv.g"
                    (file-name-directory (or load-file-name buffer-file-name)))
  "The yasmv grammar, when the tests run from a source tree.")

(defconst smv-test--model "\
#word-width 8
-- dash comment
// slash comment
MODULE counter(limit : uint8)
#hidden # hex
VAR x, y : uint8;
    s : int4[3];
VAR send-ack : boolean;
DEFINE done := x >= limit;
INIT x = 0x1F && y = 0b01 && !send-ack;
INVAR ((x << 1) <-> y) != 017 || ~x = (uint8) -1;
TRANS !done ?: x := x + 1, y := x % 3;
TRANS next(send-ack) = case done : TRUE; else : FALSE; end;
INVAR @0..3{ x <= 3 };
INVAR $1{ y > 0 };
;
MODULE main
VAR c : counter(10);
;
"
  "A model that exercises every highlighting rule.  It parses with yasmv.")

(defmacro smv-test--with-model (text &rest body)
  "Run BODY in an `smv-mode' buffer holding TEXT, fontified."
  (declare (indent 1))
  `(with-temp-buffer
     (insert ,text)
     (smv-mode)
     (font-lock-ensure)
     (goto-char (point-min))
     ,@body))

(defun smv-test--face (needle &optional occurrence offset)
  "Return the face at NEEDLE, OFFSET characters in.
OCCURRENCE picks the match, counting from 1."
  (save-excursion
    (goto-char (point-min))
    (search-forward needle nil nil (or occurrence 1))
    (get-text-property (+ (match-beginning 0) (or offset 0)) 'face)))

(ert-deftest smv-mode-highlights-model-language ()
  (smv-test--with-model smv-test--model
    (pcase-dolist (`(,needle ,occurrence ,offset ,face)
                   '(("#word-width" 1 0 font-lock-preprocessor-face)
                     ("#hidden" 1 0 font-lock-builtin-face)
                     ("# hex" 1 0 font-lock-builtin-face)
                     ("dash comment" 1 0 font-lock-comment-face)
                     ("slash comment" 1 0 font-lock-comment-face)
                     ("MODULE" 1 0 font-lock-keyword-face)
                     ("counter" 1 0 font-lock-type-face)
                     ("limit" 1 0 font-lock-variable-name-face)
                     ("uint8" 1 0 font-lock-type-face)
                     ("x, y" 1 0 font-lock-variable-name-face)
                     ("x, y" 1 3 font-lock-variable-name-face)
                     ("int4" 1 0 font-lock-type-face)
                     ("send-ack" 1 0 font-lock-variable-name-face)
                     ("boolean" 1 0 font-lock-type-face)
                     ("done" 1 0 font-lock-function-name-face)
                     ("0x1F" 1 0 font-lock-number-face)
                     ("0b01" 1 0 font-lock-number-face)
                     ("017" 1 0 font-lock-number-face)
                     ("-1;" 1 0 font-lock-operator-face)
                     ("-1;" 1 1 font-lock-number-face)
                     ("&&" 1 0 font-lock-operator-face)
                     ("<->" 1 0 font-lock-operator-face)
                     ("<<" 1 0 font-lock-operator-face)
                     ("!=" 1 0 font-lock-operator-face)
                     ("~" 1 0 font-lock-operator-face)
                     ("?:" 1 0 font-lock-keyword-face)
                     (":= x + 1" 1 0 font-lock-keyword-face)
                     ("next" 1 0 font-lock-keyword-face)
                     ("case" 1 0 font-lock-keyword-face)
                     ("else" 1 0 font-lock-keyword-face)
                     ("end;" 1 0 font-lock-keyword-face)
                     ("TRUE" 1 0 font-lock-constant-face)
                     ("FALSE" 1 0 font-lock-constant-face)
                     ("@0" 1 0 font-lock-builtin-face)
                     (".." 1 0 font-lock-operator-face)
                     ("$1" 1 0 font-lock-builtin-face)
                     ("counter" 2 0 font-lock-type-face)
                     ("10" 1 0 font-lock-number-face)
                     ("(" 1 0 font-lock-bracket-face)
                     (";" 1 0 font-lock-delimiter-face)))
      (should (equal (list needle occurrence offset
                           (smv-test--face needle occurrence offset))
                     (list needle occurrence offset face))))))

(ert-deftest smv-mode-leaves-uses-plain ()
  (smv-test--with-model smv-test--model
    ;; Assignments in TRANS are uses, not definitions.
    (should-not (smv-test--face "x := x + 1"))
    ;; The `-' in a name is not an operator.
    (should-not (smv-test--face "-ack" 2))))

(ert-deftest smv-mode-reads-names-like-the-lexer ()
  (smv-test--with-model "INVAR a->b;\nINVAR x--y;\nINVAR s = \"a -- b\";\n"
    ;; `a->b' lexes as the name `a-' followed by `>'.
    (should (eq (smv-test--face "a-") 'font-lock-warning-face))
    (should (eq (smv-test--face ">b") 'font-lock-operator-face))
    ;; `--' inside a name or a string does not start a comment.
    (should-not (smv-test--face "--y"))
    (should (eq (smv-test--face "b\"") 'font-lock-string-face))))

(ert-deftest smv-mode-flags-reserved-words ()
  (smv-test--with-model
      "VAR time : boolean; timer : boolean; goal : boolean;\nVAR input : boolean;\n-- check\n"
    (should (eq (smv-test--face "time ") 'font-lock-warning-face))
    (should (eq (smv-test--face "input") 'font-lock-warning-face))
    (should (eq (smv-test--face "timer") 'font-lock-variable-name-face))
    (should (eq (smv-test--face "goal") 'font-lock-variable-name-face))
    (should (eq (smv-test--face "check") 'font-lock-comment-face))))

(ert-deftest smv-mode-reserved-words-match-grammar ()
  "The mode reserves exactly the words the grammar reserves.
Those are the grammar's word tokens, minus the ones
`pcchar_identifier' accepts as names, plus the integer type words."
  (skip-unless (file-readable-p smv-test--grammar))
  (let* ((grammar (with-temp-buffer
                    (insert-file-contents smv-test--grammar)
                    (buffer-string)))
         (split (string-search "// -- Lexer rules" grammar))
         (parser (substring grammar 0 split))
         (lexer (substring grammar split))
         (identifier-rule
          (progn (string-match "^pcchar_identifier\\(?:.\\|\n\\)*?\n *;\n"
                               parser)
                 (match-string 0 parser)))
         (words (lambda (regexp text)
                  (let ((pos 0) found)
                    (while (string-match regexp text pos)
                      (push (match-string 1 text) found)
                      (setq pos (match-end 0)))
                    found)))
         (tokens (funcall words "'\\([A-Za-z][A-Za-z0-9_-]+\\)'" parser))
         (names (funcall words "| *'\\([A-Za-z][A-Za-z0-9_-]*\\)'"
                         identifier-rule))
         (types (funcall words ": *'\\([A-Za-z]+\\)' TYPE_WIDTH" lexer))
         (expected (seq-difference (seq-union tokens types) names))
         (known (append smv-section-keywords smv-expression-keywords
                        smv-modifiers smv-reserved-words
                        '("boolean" "int" "uint"))))
    (should names)
    (should (equal (sort (seq-uniq expected) #'string<)
                   (sort (copy-sequence known) #'string<)))))

(ert-deftest smv-mode-indents ()
  (let ((expected "\
-- header
#word-width 4
MODULE main

#inertial
VAR
    x : uint4;
    mode : { A,
             B };

DEFINE
    big := x > 3 &&
           mode = A;
    small := case x < 2 : TRUE;
                  else : FALSE;
             end;

-- next state
TRANS
    big ?:
        x := 0;

TRANS
    next(x) = case
                  big : 0;
                  else : x + 1;
              end;

INVAR x <= 3 ||
      mode = B;
;
")
        (smv-indent-offset 4))
    (with-temp-buffer
      (insert (replace-regexp-in-string "^[ \t]+" "" expected))
      (smv-mode)
      (setq indent-tabs-mode nil)
      (indent-region (point-min) (point-max))
      (should (equal (buffer-string) expected))
      ;; Indenting again changes nothing.
      (indent-region (point-min) (point-max))
      (should (equal (buffer-string) expected)))))

(ert-deftest smv-mode-comments-round-trip ()
  (let ((text "VAR x : boolean;\nINVAR x;\n"))
    (with-temp-buffer
      (insert text)
      (smv-mode)
      (comment-region (point-min) (point-max))
      (should (string-prefix-p "-- VAR" (buffer-string)))
      (uncomment-region (point-min) (point-max))
      (should (equal (buffer-string) text)))))

(ert-deftest smv-mode-builds-imenu-index ()
  (smv-test--with-model smv-test--model
    (let ((index (funcall imenu-create-index-function)))
      (should (equal (mapcar #'car (cdr (assoc "Modules" index)))
                     '("counter" "main")))
      (should (equal (mapcar #'car (cdr (assoc "Defines" index)))
                     '("done"))))))

(ert-deftest smv-mode-requires-final-newline ()
  (with-temp-buffer
    (smv-mode)
    (should require-final-newline)))

(ert-deftest smv-mode-handles-smv-files ()
  (should (eq (assoc-default "model.smv" auto-mode-alist #'string-match)
              'smv-mode)))

;;; test_smv_mode.el ends here
