;;; check-in-doom.el --- Check the :lang dx module inside a real Doom Emacs -*- lexical-binding: t; -*-

;; With the module enabled (README.org), from the checkout:
;;
;;   emacs -nw -l emacs/doom/check-in-doom.el
;;
;; (add `--init-directory DIR' when Doom is not your ~/.config/emacs).  Once
;; Doom is up, this opens a scratch .dx file, checks the module end to end
;; (eglot, the shading, popups, keys, diagnostics, the quickfix, snippets, the
;; file template, and `SPC m E' when CALC_SYMPY names a Python with SymPy),
;; writes PASS/FAIL lines to $DX_DOOM_OUT (default dx-doom-check.txt in the
;; temporary directory) and quits.  It needs a terminal or a display: Doom
;; loads no user config in --batch.

(require 'cl-lib)

(defconst dxt-root
  (expand-file-name "../../" (file-name-directory (file-truename load-file-name)))
  "The checkout.")

(defvar dxt-work (make-temp-file "dx-doom-" t))
(defvar dxt-log nil)

(defun dxt (name ok &optional info)
  (push (format "%s %s%s" (if ok "PASS" "FAIL") name
                (if info (format "  -- %S" info) ""))
        dxt-log))

(defun dxt-until (pred secs)
  (let ((end (+ (float-time) secs)))
    (while (and (not (funcall pred)) (< (float-time) end))
      (accept-process-output nil 0.1) (sit-for 0.05))
    (funcall pred)))

(defun dxt-diagnostics ()
  "The buffer's diagnostic messages: flymake's when eglot reports to it
\(without :tools lsp, or with +flymake), else flycheck's (flycheck-eglot)."
  (if (bound-and-true-p flymake-mode)
      (progn (flymake-start)
             (mapcar #'flymake-diagnostic-text
                     (flymake-diagnostics (point-min) (point-max))))
    (flycheck-buffer)
    (mapcar #'flycheck-error-message flycheck-current-errors)))

(defun dxt-run ()
  (with-temp-file (expand-file-name "s1.dx" dxt-work)
    (insert "(* readiness S1 *)\nproblem stage0.S1.\n\nftc x^3 + x^2 by ring.\nclose 2.\n"))
  (condition-case err
      (progn
        (dxt "module enabled" (modulep! :lang dx))
        (dxt "+dx-dir is the checkout" (equal +dx-dir (expand-file-name "emacs/" dxt-root)) +dx-dir)
        (find-file (expand-file-name "s1.dx" dxt-work))
        (run-hooks (quote post-command-hook)) ; eglot-ensure connects after a command
        (dxt "dx-mode" (eq major-mode 'dx-mode) major-mode)
        (dxt "calc found" (equal dx-calc-program (expand-file-name "calc" dxt-root)) dx-calc-program)
        (dxt "eglot connects" (dxt-until #'eglot-current-server 30))
        (dxt "diagnostics through flymake or flycheck"
             (or (bound-and-true-p flymake-mode) (bound-and-true-p flycheck-mode))
             (list :flycheck (bound-and-true-p flycheck-mode) :flymake (bound-and-true-p flymake-mode)))
        (dxt "checked shading (dx/progress under this eglot)"
             (dxt-until (lambda () (and (overlayp dx--checked-ov)
                                        (>= (overlay-end dx--checked-ov) (1- (point-max)))
                                        (null dx--running-ov)))
                        120)
             (and (overlayp dx--checked-ov) (overlay-end dx--checked-ov)))
        (dxt "pretty symbols are dx's" (and prettify-symbols-mode (equal prettify-symbols-alist dx-pretty-symbols)))
        (let ((ll (if (modulep! :editor evil) "SPC m" "C-c l")))
          (when (modulep! :editor evil) (evil-normal-state))
          (dxt (concat ll " l") (eq (key-binding (kbd (concat ll " l"))) '+dx/layout)
               (key-binding (kbd (concat ll " l"))))
          (dxt (concat ll " E") (eq (key-binding (kbd (concat ll " E"))) '+dx/evaluate-and-insert)))
        (dxt "C-c C-l remapped" (eq (key-binding (kbd "C-c C-l")) '+dx/layout) (key-binding (kbd "C-c C-l")))
        (goto-char (point-max))
        (+dx/layout)
        (let ((g (get-buffer-window "*dx-goals*")) (r (get-buffer-window "*dx-response*")))
          (dxt (if (modulep! :ui popup) "goals and response are popups"
                 "goals and response are shown")
               (and g r (or (not (modulep! :ui popup))
                            (and (+popup-window-p g) (+popup-window-p r)))
                    (eq (selected-window) (get-buffer-window (get-file-buffer (expand-file-name "s1.dx" dxt-work)))))
               (list g r (selected-window)))
          (dxt "stacked on the right" (and g r (= (window-left-column g) (window-left-column r))
                                           (< (window-top-line g) (window-top-line r)))))
        (dxt "goals say proved"
             (dxt-until (lambda () (dx--goals-refresh)
                          (string-prefix-p "Proved." (with-current-buffer "*dx-goals*" (buffer-string))))
                        30)
             (with-current-buffer "*dx-goals*" (buffer-substring 1 (min 60 (point-max)))))
        ;; a refusal: through flycheck or flymake into *dx-response*, then the quickfix
        (erase-buffer)
        (insert "goal Int[t = 0 .. pi] 2*t*sin t == ?A.\nftc sin t - t*cos t.\n")
        (eglot--signal-textDocument/didChange)
        (dxt "refusal is an error in the buffer"
             (dxt-until (lambda ()
                          (cl-some (lambda (m) (string-match-p "ftc-check-failed[^z]*sin t" m))
                                   (dxt-diagnostics)))
                        60)
             (dxt-diagnostics))
        (goto-char (point-min)) (search-forward "ftc")
        (setq dx--goals-at nil) (dx--goals-refresh)
        (dxt "*dx-response* shows it"
             (string-match-p "suggestion: ftc 2\\*(sin t" (with-current-buffer "*dx-response*" (buffer-string)))
             (with-current-buffer "*dx-response*" (buffer-string)))
        (dx-use-suggestion)
        (dxt "quickfix applied" (string-match-p "ftc 2\\*(sin t - t\\*cos t) by ring\\." (buffer-string)))
        (set-buffer-modified-p nil)
        (when (getenv "CALC_SYMPY")
          (erase-buffer)
          (insert "problem stage0.S1.\n")
          (eglot--signal-textDocument/didChange)
          (dxt-until (lambda () (and (overlayp dx--checked-ov) (null dx--running-ov)
                                     (>= (overlay-end dx--checked-ov) (1- (point-max))))) 60)
          (goto-char (point-max))
          (+dx/evaluate-and-insert)
          (dxt "SPC m E proves and inserts"
               (dxt-until (lambda () (string-match-p "close 2 by ring\\." (buffer-string))) 60)
               (with-current-buffer "*dx-response*" (buffer-string)))
          (dxt "response popup shown" (get-buffer-window "*dx-response*"))
          (set-buffer-modified-p nil))
        ;; snippets
        (when (modulep! :editor snippets)
          (with-temp-buffer
            (dx-mode)
            (yas-minor-mode 1)
            (insert "int_subst")
            (yas-expand)
            (dxt "int_subst snippet" (string-prefix-p "int_subst x := _ as t from _ to _ by ring." (buffer-string))
                 (buffer-string))
            (dxt "first field is active" (and yas--active-field-overlay (overlay-buffer yas--active-field-overlay))))
          (yas-reload-all)
          (with-temp-buffer
            (dx-mode) (yas-minor-mode 1) (insert "ftc") (yas-expand)
            (dxt "snippets survive yas-reload-all" (string-prefix-p "ftc _ by ring." (buffer-string)) (buffer-string))))
        ;; file template
        (when (modulep! :editor file-templates)
          (find-file (expand-file-name "new.dx" dxt-work))
          (redisplay t) (sit-for 0.5)
          (dxt "template by Doom's own hook" (> (buffer-size) 0))
          (when (= (buffer-size) 0) (+file-templates-check-h))
          (dxt "new file template" (string-prefix-p "goal Int[x = 0 .. 1] 3*x^2 + 2*x == ?A." (buffer-string))
               (buffer-string))
          (set-buffer-modified-p nil)))
    (error (dxt "no error" nil err)))
  (with-temp-file (or (getenv "DX_DOOM_OUT")
                      (expand-file-name "dx-doom-check.txt" temporary-file-directory))
    (insert (string-join (reverse dxt-log) "\n") "\n"))
  (unless (getenv "DX_DOOM_KEEP")
    (dolist (b (buffer-list))
      (with-current-buffer b (when buffer-file-name (set-buffer-modified-p nil))))
    (kill-emacs (if (cl-some (lambda (l) (string-prefix-p "FAIL" l)) dxt-log) 1 0))))

;; after Doom's startup, popups included
(add-hook 'window-setup-hook (lambda () (run-with-timer 1 nil #'dxt-run)) 90)

;;; check-in-doom.el ends here
