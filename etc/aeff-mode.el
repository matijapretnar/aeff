; Emacs mode for Æff, derived from OCaml tuareg-mode.
;
; This code could be much improved.
;
; To use the aeff-mode, put this file somewhere and add something like the following
; in your .emacs file:
;
;   (autoload 'aeff-mode "<aeff-mode-install-dir>/etc/aeff-mode" "Major mode for editing Æff files" t)
;   (setq auto-mode-alist (cons '("\\.aeff$" . aeff-mode) auto-mode-alist))

(defvar aeff-keywords
  '(
   "and"
   "as"
   "await"
   "else"
   "end"
   "fun"
   "if"
   "in"
   "let"
   "match"
   "of"
   "operation"
   "promise"
   "rec"
   "return"
   "run"
   "send"
   "then"
   "to"
   "type"
   "until"
   "use"
   "using"
   "val"
   "when"
   "with"
  ))

(defvar aeff-constants
  '(
  "false"
  "true"
  ))

(defvar aeff-types
  '(
  "bool"
  "empty"
  "int"
  "list"
  "string"
  "unit"
  ))

(defvar aeff-font-lock-defaults
    `((
      ;; stuff between "
       ("\"\\.\\*\\?" . font-lock-string-face)
      ;; prefix and infix operators, can be improved
       ("+\\|,\\|;" . font-lock-keyword-face)
       ( ,(regexp-opt aeff-keywords 'symbols) . font-lock-keyword-face)
       ( ,(regexp-opt aeff-types 'symbols) . font-lock-type-face)
       ( ,(regexp-opt aeff-constants 'symbols) . font-lock-constant-face)
      ;; highlighting signal/interrupt/operation names, can be much improved
       ("operation[ ]+\\([a-zA-Z0-9]+?\\) :" . (1 font-lock-builtin-face))
       ("promise[ ]+(\\([ ]*[a-zA-Z0-9]+?\\) " . (1 font-lock-builtin-face))
       ("send[ ]+\\([a-zA-Z0-9]+?\\) " . (1 font-lock-builtin-face))
       )))

(define-derived-mode aeff-mode
  tuareg-mode
  "Æff"
  "Major mode for Æff (rudimentary)."

  (setq font-lock-defaults aeff-font-lock-defaults)

  (setq prettify-symbols-alist '(("send" . ?↑)
                                 ("<<" . ?⟨)
                                 (">>" . ?⟩)
                                 ("|->" . ?→)
                                 ("->" . ?→)))
)

(provide 'aeff-mode)

(add-hook 'aeff-mode-hook 'prettify-symbols-mode)