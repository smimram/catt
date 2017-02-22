;; catt-mode.el -- CATT major emacs mode

(defvar catt-font-lock-keywords
 '(
   ("#.*" . 'font-lock-comment-face)
   ("\\<\\(let\\|check\\|set\\)\\>\\|:\\|=" . font-lock-keyword-face)
   ("\\<\\(Hom\\)\\>\\|->" . font-lock-builtin-face)
   ;; ("\\<\\(\\)\\>" . font-lock-constant-face)
   ("\\<let[ \t]+\\([^ (=]*\\)" 1 'font-lock-function-name-face)
  )
)

(defvar catt-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; Allow some extra characters in words
    (modify-syntax-entry ?_ "w" st)
    ;; Comments
    (modify-syntax-entry ?# "<" st)
    (modify-syntax-entry ?\n ">" st)
    st)
  "Syntax table for CATT major mode.")

(defvar catt-tab-width 4)

(define-derived-mode catt-mode fundamental-mode
  "CATT" "Major mode for CATT files."
  :syntax-table catt-mode-syntax-table
  (set (make-local-variable 'comment-start) "#")
  (set (make-local-variable 'comment-start-skip) "#+\\s-*")
  (set (make-local-variable 'font-lock-defaults) '(catt-font-lock-keywords))
  (setq mode-name "CATT")
)

(provide 'catt-mode)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.catt\\'" . catt-mode))
