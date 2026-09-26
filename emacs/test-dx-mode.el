;;; test-dx-mode.el --- ERT tests for dx-mode, against the real language server -*- lexical-binding: t; -*-

;; Run by app/test_lsp.py:
;;   emacs --batch -l dx-mode.el -l test-dx-mode.el -f ert-run-tests-batch-and-exit
;; DX_DIR holds s1.dx (stage0.S1's proof) and p3.dx (P3_LOWER's reference
;; proof), written by the Python test.

(require 'ert)
(require 'cl-lib)
(require 'flymake)
(require 'dx-mode)

(defun dx-test--until (pred &optional seconds)
  "Let the server run until PRED holds; fail after SECONDS."
  (let ((deadline (+ (float-time) (or seconds 120))))
    (while (and (not (funcall pred)) (< (float-time) deadline))
      (accept-process-output nil 0.05))
    (should (funcall pred))))

(defun dx-test--checked-end ()
  (and (overlayp dx--checked-ov) (overlay-end dx--checked-ov)))

(defun dx-test--settled-at (pos)
  "Wait until the checked prefix ends at POS and nothing runs."
  (setq pos (dx--line-end pos))
  (dx-test--until (lambda () (and (eql (dx-test--checked-end) pos)
                                  (null dx--running-ov)))))

(defun dx-test--end-of (s)
  (save-excursion (goto-char (point-min)) (search-forward s) (point)))

(defun dx-test--goals ()
  (with-current-buffer (dx--special-buffer "*dx-goals*") (buffer-string)))

(defun dx-test--response ()
  (with-current-buffer (dx--special-buffer "*dx-response*") (buffer-string)))

(defun dx-test--goals-at (pos prefix)
  "Move to POS and wait until *dx-goals* starts with PREFIX."
  (goto-char pos)
  (dx-test--until (lambda () (dx--goals-refresh)
                    (string-prefix-p prefix (dx-test--goals)))))

(defmacro dx-test--visit (name &rest body)
  "Visit DX_DIR/NAME in dx-mode, connected through eglot; run BODY."
  (declare (indent 1))
  `(let* ((file (expand-file-name ,name (getenv "DX_DIR")))
          (buf (find-file-noselect file)))
     (unwind-protect
         (with-current-buffer buf
           (should (derived-mode-p 'dx-mode))
           (unless (eglot-current-server)
             (apply #'eglot (eglot--guess-contact)))
           (dx-test--until #'eglot-current-server 30)
           ,@body)
       (with-current-buffer buf
         (set-buffer-modified-p nil)
         (let ((server (eglot-current-server)))
           (when server (eglot-shutdown server))))
       (let ((kill-buffer-query-functions nil)) (kill-buffer buf)))))

(ert-deftest dx-s1-checks-and-the-goals-say-proved ()
  (dx-test--visit "s1.dx"
    (should (eq (eglot-current-server)
                (with-current-buffer (current-buffer) (eglot-current-server))))
    (dx-test--settled-at (dx-test--end-of "close 2."))
    (dx-test--goals-at (point-max) "Proved.")
    ;; inside the ftc sentence: the header's goal, not yet proved
    (dx-test--goals-at (1+ (dx-test--end-of "stage0.S1.")) "Open")
    (should (string-match-p "Int\\[x = 0 \\.\\. 1\\]" (dx-test--goals)))))

(ert-deftest dx-a-refusal-is-a-flymake-error-and-the-quickfix-fixes-it ()
  (dx-test--visit "s1.dx"
    (dx-test--settled-at (dx-test--end-of "close 2."))
    (erase-buffer)
    (insert "goal Int[t = 0 .. pi] 2*t*sin t == ?A.\nftc sin t - t*cos t.\n")
    (eglot--signal-textDocument/didChange) ; eglot's idle timer, in batch
    (dx-test--settled-at (dx-test--end-of "?A."))
    (dx-test--until
     (lambda ()
       (flymake-start)
       (seq-some (lambda (d) (and (eq (flymake-diagnostic-type d) 'eglot-error)
                                  (string-match-p "ftc-check-failed"
                                                  (flymake-diagnostic-text d))))
                 (flymake-diagnostics (point-min) (point-max)))))
    (goto-char (point-min))
    (search-forward "ftc")
    (setq dx--goals-at nil)
    (dx--goals-refresh)
    (should (string-match-p "suggestion: ftc 2\\*(sin t" (dx-test--response)))
    (dx-use-suggestion)
    (eglot--signal-textDocument/didChange)
    (should (string-match-p "ftc 2\\*(sin t - t\\*cos t) by ring\\."
                            (buffer-string)))
    (dx-test--settled-at (dx-test--end-of "by ring."))))

(ert-deftest dx-hint-rungs-climb-at-the-same-goal ()
  (dx-test--visit "s1.dx"
    (dx-test--settled-at (dx-test--end-of "close 2."))
    (goto-char (1+ (dx-test--end-of "stage0.S1.")))
    (dx-hint)
    (dx-test--until (lambda () (string-prefix-p "Hint ? " (dx-test--response))))
    (dx-hint)
    (dx-test--until (lambda () (string-prefix-p "Hint ?? " (dx-test--response))))))

(ert-deftest dx-p3-lower-proves ()
  (dx-test--visit "p3.dx"
    (dx-test--settled-at (save-excursion (goto-char (point-max))
                                         (skip-chars-backward " \n")
                                         (point)))
    (dx-test--goals-at (point-max) "Proved.")))

(ert-deftest dx-complete-inserts-the-template ()
  (with-temp-buffer
    (dx-mode)
    (insert "int_s")
    (cl-letf (((symbol-function 'completing-read)
               (lambda (&rest _) "int_subst")))
      (dx-complete))
    (should (equal (buffer-string) "int_subst x := _ as t from _ to _ by ring."))
    (should (eq (char-after) ?_))))

(ert-deftest dx-pretty-display-keeps-the-text ()
  (with-temp-buffer
    (insert "close pi/4 + Int[x = 0 .. oo] sqrt x.")
    (dx-mode)
    (font-lock-ensure)
    (should prettify-symbols-mode)
    (should (equal (buffer-string) "close pi/4 + Int[x = 0 .. oo] sqrt x."))
    (goto-char (point-min))
    (search-forward "pi")
    (should (get-text-property (1- (point)) 'composition))))

(ert-deftest dx-templates-match-the-server ()
  "The offline templates are the server's (script.TEMPLATES)."
  (dx-test--visit "s1.dx"
    (let* ((items (plist-get (jsonrpc-request
                              (eglot-current-server) :textDocument/completion
                              (list :textDocument (eglot--TextDocumentIdentifier)
                                    :position (eglot--pos-to-lsp-position)))
                             :items))
           (server (mapcar (lambda (i) (cons (plist-get i :label)
                                             (plist-get i :detail)))
                           items)))
      (should (equal (sort (copy-sequence server)
                           (lambda (a b) (string< (car a) (car b))))
                     (sort (copy-sequence dx-templates)
                           (lambda (a b) (string< (car a) (car b)))))))))

(ert-deftest dx-evaluate-proves-and-inserts ()
  "EVAL.md: C-c C-e at the header's end writes the value; C-u inserts the
checked sentences right there."
  (skip-unless (getenv "CALC_SYMPY"))
  (dx-test--visit "s1.dx"
    (dx-test--settled-at (dx-test--end-of "close 2."))
    (erase-buffer)
    (insert "problem stage0.S1.\n")
    (eglot--signal-textDocument/didChange)
    (dx-test--settled-at (dx-test--end-of "stage0.S1."))
    (goto-char (point-max))
    (dx-evaluate '(4))
    (dx-test--until (lambda () (string-prefix-p "Proved by the kernel"
                                                (dx-test--response))))
    (should (string-match-p "= 2" (dx-test--response)))
    (dx-test--until (lambda () (string-match-p "close 2 by ring\\." (buffer-string))))
    (eglot--signal-textDocument/didChange)
    (dx-test--settled-at (dx-test--end-of "close 2 by ring."))
    (dx-test--goals-at (point-max) "Proved.")
    (set-buffer-modified-p nil)))

(defvar flycheck-mode)                  ; not loaded here: bind it dynamically

(ert-deftest dx-reads-flycheck-when-flymake-is-off ()
  "Doom Emacs shows eglot's diagnostics through flycheck, not flymake."
  (with-temp-buffer
    (dx-mode)
    (insert "ftc x.\n")
    (goto-char (point-min))
    (let ((flymake-mode nil) (flycheck-mode t) (asked nil))
      (cl-letf (((symbol-function 'flycheck-overlay-errors-in)
                 (lambda (beg end) (setq asked (list beg end)) '(e1 e1)))
                ((symbol-function 'flycheck-error-message)
                 (lambda (_) "ftc-check-failed: here")))
        (dx--show-diagnostics-here)
        (should (equal asked (list 1 8)))
        (should (equal (dx-test--response) "ftc-check-failed: here"))))))

(ert-deftest dx-docver-under-either-eglot ()
  (with-temp-buffer
    (if (boundp 'eglot--docver)
        (let ((eglot--docver 7)) (should (eql (dx--docver) 7)))
      (let ((eglot--versioned-identifier 7)) (should (eql (dx--docver) 7))))))

;;; test-dx-mode.el ends here
