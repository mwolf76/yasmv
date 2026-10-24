;;; smv-mode.el --- Major mode for yasmv models  -*- lexical-binding: t; -*-

;; This file is part of the yasmv distribution
;; (c) 2011-2026 M. Pensallorto < marco DOT pensallorto AT gmail DOT com >

;; Keywords: languages
;; Package-Requires: ((emacs "29.1"))

;;; Commentary:

;; Editing support for the yasmv dialect of SMV: highlighting,
;; indentation, comments and imenu.  The lexical rules follow the
;; grammar in src/parser/grammars/smv.g:
;;
;; - A name starts with a letter or `_' and continues with letters,
;;   digits, `_', `-', `#' and `$'.  So `send-ack' is one name, and so
;;   is the `a-' in `a->b'.  Names ending in `-' are flagged, because
;;   they are almost always a missing space.
;; - `--' and `//' start a comment, except inside a name.
;; - The interactive shell and the model parser share one lexer, so
;;   shell words such as `check', `time' or `init' are reserved in
;;   models.  Using one as a name is flagged.
;;
;; Installation:
;;
;;   (add-to-list 'load-path "/path/to/yasmv/tools")
;;   (require 'smv-mode)
;;
;; Tests, from the repository root:
;;
;;   emacs -Q --batch -l tools/smv-mode.el -l tests/test_smv_mode.el \
;;     -f ert-run-tests-batch-and-exit

;;; Code:

(defgroup smv nil
  "Editing yasmv models."
  :group 'languages
  :prefix "smv-")

(defcustom smv-indent-offset 4
  "Indentation step for section bodies, `case' clauses and continuations."
  :type 'integer
  :safe #'integerp)

;;;; Vocabulary

(defconst smv-section-keywords
  '("MODULE" "VAR" "DEFINE" "INIT" "INVAR" "TRANS")
  "Keywords that open a module or one of its sections.")

(defconst smv-expression-keywords '("case" "else" "end" "next")
  "Keywords used inside expressions.")

(defconst smv-modifiers
  '("hidden" "frozen" "inertial" "input" "bin" "oct" "dec" "hex")
  "Declaration modifiers, written after `#'.")

(defconst smv-reserved-words
  '("check" "clear" "compare-traces" "diameter" "do" "dump-model"
    "dump-trace" "dup-trace" "echo" "explain-init" "explain-reach"
    "explain-step" "export-progress" "failure" "get" "help" "init"
    "invariant" "last" "list-traces" "on" "pick-state" "progress" "quit"
    "reachable" "read-model" "read-trace" "reset" "save" "select-trace"
    "set" "settings" "show-symbols" "simulate" "state" "success" "time"
    "trans" "unlimited" "validate-progress")
  "Shell words that the lexer also reserves in models.")

(defconst smv--name-regexp "[A-Za-z_][A-Za-z0-9_#$-]*"
  "Regexp matching a name, as the lexer reads it.")

(defconst smv--section-regexp (regexp-opt smv-section-keywords 'symbols)
  "Regexp matching a section keyword.  Group 1 holds the keyword.")

;;;; Syntax

(defvar smv-mode-syntax-table
  (let ((table (make-syntax-table)))
    ;; Characters that continue a name.
    (dolist (c '(?_ ?- ?# ?$))
      (modify-syntax-entry c "_" table))
    ;; Strings take either quote and have no escapes.
    (modify-syntax-entry ?\" "\"" table)
    (modify-syntax-entry ?' "\"" table)
    (modify-syntax-entry ?\\ "." table)
    ;; Comments end at the newline. `smv--syntax-propertize' marks
    ;; where they start, because `-' also continues names.
    (modify-syntax-entry ?\n ">" table)
    (dolist (c '(?@ ?. ?? ?: ?\; ?, ?! ?~ ?^ ?& ?| ?% ?* ?+ ?/ ?= ?< ?>))
      (modify-syntax-entry c "." table))
    table)
  "Syntax table for `smv-mode'.")

(defun smv--inside-name-p (pos)
  "Return non-nil if the character at POS continues a name."
  (save-excursion
    (goto-char pos)
    (skip-chars-backward "A-Za-z0-9_#$-")
    (and (< (point) pos)
         (looking-at-p "[A-Za-z_]"))))

(defun smv--comment-start-syntax ()
  "Return the syntax opening a comment at the matched `--' or `//', or nil.
The pair starts a comment unless it is in a string or comment
already, or continues a name."
  (let ((start (match-beginning 0)))
    (unless (or (nth 8 (save-excursion (syntax-ppss start)))
                (and (eq (char-after start) ?-)
                     (smv--inside-name-p start)))
      (string-to-syntax "<"))))

(defconst smv--syntax-propertize
  (syntax-propertize-rules
   ("\\(-\\)-" (1 (smv--comment-start-syntax)))
   ("\\(/\\)/" (1 (smv--comment-start-syntax))))
  "Mark the characters that start comments.")

(defun smv--code-p (pos)
  "Return non-nil if POS is outside comments and strings."
  (not (nth 8 (save-excursion (syntax-ppss pos)))))

(defun smv--comment-start-p ()
  "Return non-nil if a comment starts at point."
  (and (looking-at-p "--\\|//")
       (nth 4 (save-excursion (syntax-ppss (1+ (point)))))))

(defun smv--section ()
  "Return (KEYWORD . POSITION) of the section keyword before point."
  (save-excursion
    (let ((case-fold-search nil)
          found)
      (while (and (not found)
                  (re-search-backward smv--section-regexp nil t))
        (let ((keyword (match-string-no-properties 1)))
          (when (smv--code-p (point))
            (setq found (cons keyword (point))))))
      found)))

;;;; Highlighting

(defun smv--module-header-paren-p (open)
  "Return non-nil if the paren at OPEN opens a MODULE parameter list."
  (save-excursion
    (goto-char open)
    (skip-chars-backward " \t")
    (skip-chars-backward "A-Za-z0-9_#$-")
    (skip-chars-backward " \t\n")
    (looking-back "\\_<MODULE" (max (point-min) (- (point) 6)))))

(defun smv--declaration-p (pos)
  "Return non-nil if the names starting at POS are being declared.
They are declared at the start of a VAR clause or in a MODULE
parameter list."
  (save-excursion
    (let ((ppss (syntax-ppss pos)))
      (unless (nth 8 ppss)
        (goto-char pos)
        (forward-comment (- (point)))
        (pcase (car ppss)
          (0 (and (equal (car (smv--section)) "VAR")
                  (or (memq (char-before) '(?\; ?,))
                      (looking-back "\\_<VAR" (max (point-min)
                                                   (- (point) 3))))))
          (1 (and (memq (char-before) '(?\( ?,))
                  (smv--module-header-paren-p (nth 1 ppss)))))))))

(defconst smv--declared-names-regexp
  (concat "\\_<\\(" smv--name-regexp
          "\\(?:[ \t\n]*,[ \t\n]*" smv--name-regexp "\\)*\\)"
          "[ \t\n]*:\\(?:[^=]\\|\\'\\)")
  "Regexp matching `NAMES :' in a declaration.  Group 1 holds NAMES.")

(defun smv--match-declared-names (limit)
  "Find the next list of declared names before LIMIT."
  (let (found)
    (while (and (not found)
                (re-search-forward smv--declared-names-regexp limit t))
      (setq found (save-match-data
                    (smv--declaration-p (match-beginning 1))))
      (goto-char (match-end 1)))
    found))

(defun smv--match-defined-name (limit)
  "Find the next name defined in a DEFINE section before LIMIT."
  (let ((regexp (concat "\\_<\\(" smv--name-regexp "\\)[ \t\n]*:="))
        found)
    (while (and (not found) (re-search-forward regexp limit t))
      (let ((pos (match-beginning 1)))
        (setq found
              (save-match-data
                (save-excursion
                  (let ((ppss (syntax-ppss pos)))
                    (and (not (nth 8 ppss))
                         (zerop (car ppss))
                         (progn (goto-char pos)
                                (forward-comment (- (point)))
                                (or (eq (char-before) ?\;)
                                    (looking-back "\\_<DEFINE"
                                                  (max (point-min)
                                                       (- (point) 6)))))
                         (equal (car (smv--section)) "DEFINE"))))))))
    found))

(defun smv--match-instance-type (limit)
  "Find the next module instance type in a VAR section before LIMIT."
  (let ((regexp (concat ":[ \t\n]*\\(" smv--name-regexp "\\)[ \t\n]*("))
        found)
    (while (and (not found) (re-search-forward regexp limit t))
      (let ((pos (match-beginning 1)))
        (setq found
              (save-match-data
                (save-excursion
                  (let ((ppss (syntax-ppss pos)))
                    (and (not (nth 8 ppss))
                         (zerop (car ppss))
                         (progn (goto-char pos)
                                (equal (car (smv--section)) "VAR")))))))))
    found))

(defconst smv--number-regexp
  "\\(?:0[xX][0-9a-fA-F]+\\|0[bB][01]+\\|[0-9]+\\)\\_>"
  "Regexp matching a hexadecimal, binary, octal or decimal literal.")

(defun smv--match-number (limit)
  "Find the next numeric literal before LIMIT, skipping digits in names."
  (let (found)
    (while (and (not found)
                (re-search-forward smv--number-regexp limit t))
      (setq found (not (smv--inside-name-p (match-beginning 0)))))
    found))

(defconst smv--operator-regexp
  (regexp-opt '("<->" "->" "||" "&&" "!=" "<=" ">=" "<<" ">>" ".."
                "=" "<" ">" "+" "-" "*" "/" "%" "&" "|" "^" "~" "!" "?"))
  "Regexp matching an operator.")

(defun smv--match-operator (limit)
  "Find the next operator before LIMIT, skipping `-' inside names."
  (let (found)
    (while (and (not found)
                (re-search-forward smv--operator-regexp limit t))
      (if (and (eq (char-after (match-beginning 0)) ?-)
               (smv--inside-name-p (match-beginning 0)))
          (goto-char (1+ (match-beginning 0)))
        (setq found t)))
    found))

(defconst smv-font-lock-keywords
  `(("\\_<#word-width\\_>" . 'font-lock-preprocessor-face)
    (,(concat "\\_<#[ \t]*" (regexp-opt smv-modifiers) "\\_>")
     . 'font-lock-builtin-face)
    (,(concat "\\_<" smv--name-regexp "-\\_>") . 'font-lock-warning-face)
    (,(regexp-opt (append smv-reserved-words smv-modifiers) 'symbols)
     . 'font-lock-warning-face)
    (,(regexp-opt (append smv-section-keywords smv-expression-keywords)
                  'symbols)
     . 'font-lock-keyword-face)
    ("?:\\|:=" . 'font-lock-keyword-face)
    (,(concat "\\_<MODULE[ \t]+\\(" smv--name-regexp "\\)")
     1 'font-lock-type-face)
    (smv--match-declared-names
     (,(concat "\\_<" smv--name-regexp)
      (progn (goto-char (match-beginning 1)) (match-end 1))
      (goto-char (match-end 0))
      (0 'font-lock-variable-name-face)))
    (smv--match-defined-name 1 'font-lock-function-name-face)
    (smv--match-instance-type 1 'font-lock-type-face)
    ("\\_<\\(?:boolean\\|u?int[0-9]*\\)\\_>" . 'font-lock-type-face)
    ("\\_<\\(?:TRUE\\|FALSE\\)\\_>" . 'font-lock-constant-face)
    ("\\(?:@\\|\\_<\\$\\)[0-9]+" . 'font-lock-builtin-face)
    (smv--match-number . 'font-lock-number-face)
    (smv--match-operator . 'font-lock-operator-face)
    ("[][(){}]" . 'font-lock-bracket-face)
    ("[;,:]" . 'font-lock-delimiter-face))
  "Highlighting rules for `smv-mode'.  Earlier rules take precedence.")

;;;; Indentation

(defun smv--top-level-line-p ()
  "Return non-nil if the code at point starts a top-level line.
Such lines open a module or a section, hold a directive or a
modifier, or end a module with a lone `;'."
  (let ((case-fold-search nil))
    (or (looking-at-p smv--section-regexp)
        (looking-at-p "#")
        (looking-at-p ";[ \t]*\\(?:$\\|--\\|//\\)"))))

(defun smv--previous-code-line ()
  "Move to the indentation of the previous line holding code.
Return nil if there is none."
  (let (found)
    (while (and (not found) (zerop (forward-line -1)))
      (back-to-indentation)
      (unless (or (eolp) (smv--comment-start-p))
        (setq found t)))
    found))

(defun smv--next-code-line ()
  "Move to the indentation of the next line holding code.
Return nil if there is none."
  (let (found)
    (while (and (not found) (zerop (forward-line 1)) (not (eobp)))
      (back-to-indentation)
      (unless (or (eolp) (smv--comment-start-p))
        (setq found t)))
    found))

(defun smv--line-code-end ()
  "Return the position after the last code character on this line."
  (save-excursion
    (end-of-line)
    (let ((ppss (syntax-ppss)))
      (when (nth 4 ppss)
        (goto-char (nth 8 ppss))))
    (skip-chars-backward " \t")
    (point)))

(defun smv--enclosing-case (bound)
  "Return the position of the unclosed `case' before point, after BOUND."
  (save-excursion
    (let ((case-fold-search nil)
          (depth (car (syntax-ppss)))
          (nesting 0)
          found)
      (while (and (not found)
                  (re-search-backward "\\_<\\(case\\|end\\)\\_>" bound t))
        (let ((word (match-string-no-properties 1))
              (ppss (save-excursion (syntax-ppss (match-beginning 0)))))
          (when (and (not (nth 8 ppss)) (= (car ppss) depth))
            (cond ((equal word "end") (setq nesting (1+ nesting)))
                  ((zerop nesting) (setq found (point)))
                  (t (setq nesting (1- nesting)))))))
      found)))

(defun smv--statement-start (bound)
  "Return the position of the first token of the statement at point.
Statements end with a `;' outside `case' blocks.  BOUND is the
end of the section keyword."
  (save-excursion
    (let ((case-fold-search nil)
          (nesting 0)
          found)
      (while (and (not found)
                  (re-search-backward "\\(;\\)\\|\\_<\\(case\\|end\\)\\_>"
                                      bound t))
        (let ((semicolon (match-beginning 1))
              (word (match-string-no-properties 2))
              (ppss (save-excursion (syntax-ppss (match-beginning 0)))))
          (when (and (not (nth 8 ppss)) (zerop (car ppss)))
            (cond ((equal word "end") (setq nesting (1+ nesting)))
                  (word (setq nesting (max 0 (1- nesting))))
                  ((zerop nesting) (setq found (1+ semicolon)))))))
      (goto-char (or found bound))
      (forward-comment (buffer-size))
      (point))))

(defun smv--paren-indentation (open)
  "Return the indentation for a line inside the paren at OPEN."
  (let ((closing (looking-at-p "[])}]")))
    (save-excursion
      (goto-char open)
      (let ((open-column (current-column)))
        (forward-char)
        (skip-chars-forward " \t")
        (cond ((or (eolp) (smv--comment-start-p))
               (+ (current-indentation) (if closing 0 smv-indent-offset)))
              (closing open-column)
              (t (current-column)))))))

(defun smv--case-indentation (case-pos)
  "Return the indentation for a line inside the `case' at CASE-POS.
Clauses align with the first one when it shares the `case' line,
else they indent one step from `case'."
  (let* ((case-column (save-excursion (goto-char case-pos) (current-column)))
         (clause-column
          (save-excursion
            (goto-char (+ case-pos 4))
            (skip-chars-forward " \t")
            (if (or (eolp) (smv--comment-start-p))
                (+ case-column smv-indent-offset)
              (current-column)))))
    (cond ((looking-at-p "end\\_>") case-column)
          ((save-excursion
             (forward-comment (- (point)))
             (or (eq (char-before) ?\;)
                 (<= (point) (+ case-pos 4))))
           clause-column)
          (t (+ clause-column smv-indent-offset)))))

(defun smv--statement-indentation (section)
  "Return the indentation for a line of the statement at point.
SECTION is (KEYWORD . POSITION) of the enclosing section."
  (let* ((bound (+ (cdr section) (length (car section))))
         (start (smv--statement-start bound))
         (previous (save-excursion
                     (and (smv--previous-code-line) (point)))))
    (cond
     ((or (null previous)
          (save-excursion
            (goto-char previous)
            (looking-at-p ";[ \t]*\\(?:$\\|--\\|//\\)")))
      0)
     ;; The first line of a statement: align with the first clause
     ;; when it shares the keyword's line, else indent one step.
     ((>= start (point))
      (save-excursion
        (goto-char bound)
        (skip-chars-forward " \t")
        (if (or (eolp) (smv--comment-start-p))
            (+ (current-indentation) smv-indent-offset)
          (current-column))))
     ;; After `?:' or `:=' at the end of a line, indent one step.
     ((save-excursion
        (goto-char previous)
        (goto-char (smv--line-code-end))
        (looking-back "?:\\|:=" (max (point-min) (- (point) 2))))
      (+ (save-excursion (goto-char start) (current-column))
         smv-indent-offset))
     ;; The second line of a statement: align with the text after the
     ;; first `?:' or `:=', or with the statement itself.
     ((= (line-number-at-pos previous) (line-number-at-pos start))
      (save-excursion
        (goto-char start)
        (let ((end (smv--line-code-end))
              column)
          (while (and (not column)
                      (re-search-forward "?:\\|:=" end t))
            (let ((operator (match-beginning 0))
                  (after (match-end 0)))
              (when (and (smv--code-p operator)
                         (zerop (car (save-excursion
                                       (syntax-ppss operator)))))
                (goto-char after)
                (skip-chars-forward " \t")
                (when (< (point) end)
                  (setq column (current-column))))
              (goto-char after)))
          (or column
              (progn (goto-char start) (current-column))))))
     ;; Later lines keep the alignment of the line before.
     (t (save-excursion (goto-char previous) (current-column))))))

(defun smv--code-indentation ()
  "Return the indentation for the code line at point."
  (if (smv--top-level-line-p)
      0
    (let* ((ppss (syntax-ppss))
           (open (nth 1 ppss))
           (section (smv--section))
           (bound (if section
                      (+ (cdr section) (length (car section)))
                    (point-min)))
           (case-pos (smv--enclosing-case (max bound (or open bound)))))
      (cond
       ((and case-pos (or (null open) (> case-pos open)))
        (smv--case-indentation case-pos))
       (open (smv--paren-indentation open))
       ((or (null section) (equal (car section) "MODULE")) 0)
       (t (smv--statement-indentation section))))))

(defun smv--indentation ()
  "Return the indentation for the current line."
  (save-excursion
    (back-to-indentation)
    (let ((case-fold-search nil))
      (smv--line-indentation))))

(defun smv--line-indentation ()
  "Return the indentation for the line whose indentation is at point."
  (cond
   ((nth 3 (syntax-ppss)) (current-indentation))
   ;; A comment followed by a top-level line documents that line.
   ((and (smv--comment-start-p)
         (save-excursion
           (and (smv--next-code-line) (smv--top-level-line-p))))
    0)
   (t (smv--code-indentation))))

(defun smv-indent-line ()
  "Indent the current line of a yasmv model."
  (interactive)
  (let ((indent (smv--indentation))
        (from-end (- (point-max) (point))))
    (indent-line-to indent)
    (when (> (- (point-max) from-end) (point))
      (goto-char (- (point-max) from-end)))))

;;;; Imenu

(defun smv--imenu-create-index ()
  "Return an imenu index of the modules and defines in the buffer."
  (let ((case-fold-search nil)
        (module-regexp (concat "\\_<MODULE[ \t]+\\(" smv--name-regexp "\\)"))
        modules defines)
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward module-regexp nil t)
        (let ((name (match-string-no-properties 1))
              (pos (match-beginning 1)))
          (when (smv--code-p pos)
            (push (cons name pos) modules))))
      (goto-char (point-min))
      (while (smv--match-defined-name (point-max))
        (push (cons (match-string-no-properties 1) (match-beginning 1))
              defines)))
    (delq nil (list (and modules (cons "Modules" (nreverse modules)))
                    (and defines (cons "Defines" (nreverse defines)))))))

;;;; Mode

;;;###autoload
(define-derived-mode smv-mode prog-mode "SMV"
  "Major mode for editing yasmv models.

Highlights the model language and flags names the lexer reads
differently than intended: shell words, which are reserved, and
names ending in `-', as in `a->b'.  Indentation steps by
`smv-indent-offset'.  Files always end with a newline, because a
comment on a last line without one is a syntax error.

\\{smv-mode-map}"
  (setq-local comment-start "-- ")
  (setq-local comment-end "")
  (setq-local comment-start-skip "\\(?:--+\\|//+\\)[ \t]*")
  (setq-local syntax-propertize-function smv--syntax-propertize)
  (setq-local font-lock-defaults '(smv-font-lock-keywords))
  (setq-local indent-line-function #'smv-indent-line)
  (setq-local imenu-create-index-function #'smv--imenu-create-index)
  (setq-local require-final-newline mode-require-final-newline))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.smv\\'" . smv-mode))

(provide 'smv-mode)
;;; smv-mode.el ends here
