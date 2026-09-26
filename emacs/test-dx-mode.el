;;; test-dx-mode.el --- ERT tests for dx-mode, against the real checker -*- lexical-binding: t; -*-

;; Run by app/test_dx.py:
;;   emacs --batch -l dx-mode.el -l test-dx-mode.el -f ert-run-tests-batch-and-exit
;; DX_SENTENCES names app/sentences.json; DX_P3 a .dx file of P3_LOWER's
;; reference proof, written by the Python test.

(require 'ert)
(require 'cl-lib)
(require 'dx-mode)

(defun dx-test--wait (&optional seconds)
  "Wait until nothing runs or is queued, and no answer is outstanding."
  (let ((deadline (+ (float-time) (or seconds 120))))
    (while (and (or dx--busy dx--queue dx--callbacks)
                (< (float-time) deadline))
      (accept-process-output dx--proc 0.05))
    (should-not dx--busy)))

(defmacro dx-test--with (text &rest body)
  "Run BODY in a dx-mode buffer holding TEXT, then stop its checker."
  (declare (indent 1))
  `(let ((buf (generate-new-buffer "test.dx")))
     (unwind-protect
         (with-current-buffer buf
           (insert ,text)
           (dx-mode)
           (goto-char (point-min))
           ,@body)
       (with-current-buffer buf (dx-exit))
       (let ((kill-buffer-query-functions nil)) (kill-buffer buf)))))

(defun dx-test--goals ()
  (with-current-buffer "*dx-goals*" (buffer-string)))

(defun dx-test--response ()
  (with-current-buffer "*dx-response*" (buffer-string)))

(defun dx-test--end-of (s)
  "The position just after the first occurrence of S."
  (save-excursion (goto-char (point-min)) (search-forward s) (point)))

(defconst dx-test--s1
  "(* readiness S1 *)\nproblem stage0.S1.\n\nftc x^3 + x^2 by ring.\nclose 2.\n")

(ert-deftest dx-sentences-match-the-fixture ()
  "DX.md review 4: the splitter gives app/sentences.json's spans."
  (let ((cases (alist-get 'cases (json-parse-string
                                  (with-temp-buffer
                                    (insert-file-contents (getenv "DX_SENTENCES"))
                                    (buffer-string))
                                  :object-type 'alist :array-type 'list))))
    (should (> (length cases) 5))
    (dolist (c cases)
      (with-temp-buffer
        (insert (alist-get 'text c))
        (let ((at (point-min)) s spans)
          (while (setq s (dx--next-sentence at))
            (push (list (1- (car s)) (1- (cdr s))) spans)
            (setq at (cdr s)))
          (should (equal (list (alist-get 'text c) (nreverse spans))
                         (list (alist-get 'text c) (alist-get 'spans c)))))))))

(ert-deftest dx-s1-proves-to-the-end ()
  (dx-test--with dx-test--s1
    (dx-goto-end)
    (dx-test--wait)
    (should (= (dx--locked-end) (dx-test--end-of "close 2.")))
    (should (equal (length dx--path) 3))
    (should (string-prefix-p "Proved." (dx-test--goals)))
    (should (string-match-p "n2: close accepted" (dx-test--response)))
    (should (overlayp dx--locked-ov))))

(ert-deftest dx-next-undo-and-goto-point ()
  (dx-test--with dx-test--s1
    (dx-next) (dx-test--wait)
    (should (= (dx--locked-end) (dx-test--end-of "stage0.S1.")))
    (should (string-match-p "Open: Int" (dx-test--goals)))
    (dx-next) (dx-test--wait)
    (should (= (dx--locked-end) (dx-test--end-of "by ring.")))
    (dx-undo) (dx-test--wait)
    (should (= (dx--locked-end) (dx-test--end-of "stage0.S1.")))
    (goto-char (point-max))
    (dx-goto-point) (dx-test--wait)
    (should (string-prefix-p "Proved." (dx-test--goals)))
    ;; the undone node was kept, as the API keeps it: n1 retracted, then n2, n3
    (should (equal dx--path '("n0" "n2" "n3")))
    (goto-char (dx-test--end-of "stage0.S1."))
    (dx-goto-point) (dx-test--wait)
    (should (= (length dx--done) 1))
    (dx-retract-all)
    (should (null dx--session))
    (should (= (dx--locked-end) (point-min)))))

(ert-deftest dx-refusal-and-suggestion ()
  (dx-test--with "problem stage0.S1.\nftc 2*x^3 + 2*x^2 by ring.\nclose 2.\n"
    (dx-goto-end)
    (dx-test--wait)
    (should (= (length dx--done) 1))
    (should (overlayp dx--error-ov))
    (should (string-match-p "ftc-check-failed" (dx-test--response)))
    (should (string-match-p "Suggestion (C-c C-a)" (dx-test--response)))
    (dx-use-suggestion)
    (should (string-match-p "ftc (2\\*x^3 \\+ 2\\*x^2)/2 by ring\\." (buffer-string)))
    (should-not dx--error-ov)
    (dx-goto-end)
    (dx-test--wait)
    (should (string-prefix-p "Proved." (dx-test--goals)))))

(ert-deftest dx-edits-retract ()
  (dx-test--with dx-test--s1
    (dx-goto-end) (dx-test--wait)
    ;; `close 2.' + `5': an insertion right after the last `.' edits it
    (goto-char (dx-test--end-of "close 2."))
    (insert "5")
    (should (= (length dx--done) 2))
    (delete-char -1)
    (dx-goto-end) (dx-test--wait)
    (should (= (length dx--done) 3))
    ;; a newline after the locked end changes nothing
    (goto-char (dx-test--end-of "close 2."))
    (insert "\n")
    (should (= (length dx--done) 3))
    ;; an edit inside ftc's sentence retracts to it, and undo is plain text
    (undo-boundary)
    (goto-char (dx-test--end-of "x^3"))
    (insert "0")
    (should (= (length dx--done) 1))
    (should (= (dx--locked-end) (dx-test--end-of "stage0.S1.")))
    (undo-boundary)
    (let ((last-command nil)) (undo))
    (should (string-match-p "ftc x^3 \\+ x^2" (buffer-string)))
    ;; yank into the locked header drops the session
    (goto-char (dx-test--end-of "problem"))
    (kill-new " ")
    (yank)
    (should (null dx--session))
    (should (= (dx--locked-end) (point-min)))))

(ert-deftest dx-locked-text-is-read-only-while-busy ()
  (dx-test--with dx-test--s1
    (dx-next) (dx-test--wait)
    (dx-goto-end)
    (should dx--busy)
    (goto-char (point-min))
    (should-error (insert "x") :type 'text-read-only)
    (dx-test--wait)
    (should (string-prefix-p "Proved." (dx-test--goals)))
    (goto-char (point-min))
    (insert " ")
    (should (null dx--session))))

(ert-deftest dx-goal-header-with-functions ()
  (dx-test--with "goal Int[x = 0 .. 1] f(x) == ?A functions f/1.\n"
    (dx-next) (dx-test--wait)
    (should dx--session)
    (should (string-match-p "f(x)" (dx-test--goals)))))

(ert-deftest dx-bad-header-and-unknown-problem ()
  (dx-test--with "ftc x by ring.\n"
    (dx-next) (dx-test--wait)
    (should (null dx--session))
    (should (string-match-p "bad-header" (dx-test--response))))
  (dx-test--with "problem no.such.problem.\n"
    (dx-next) (dx-test--wait)
    (should (null dx--session))
    (should (string-match-p "unknown-problem" (dx-test--response)))))

(ert-deftest dx-hint-rungs ()
  (dx-test--with "problem parts.P1_PARTS.\n"
    (dx-next) (dx-test--wait)
    (dx-hint) (dx-test--wait)
    (should (string-match-p "Hint \\? .*\nA substitution\\." (dx-test--response)))
    (dx-hint) (dx-test--wait)
    (should (string-match-p "Hint \\?\\? " (dx-test--response)))
    (dx-hint 1) (dx-test--wait)
    (should (string-match-p "Hint \\? " (dx-test--response)))))

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

(ert-deftest dx-p3-lower-proves ()
  (let ((file (getenv "DX_P3")))
    (skip-unless file)
    (dx-test--with (with-temp-buffer (insert-file-contents file) (buffer-string))
      (dx-goto-end)
      (dx-test--wait 300)
      (should (string-prefix-p "Proved." (dx-test--goals)))
      (should (string-match-p "(5/16)\\*b^6 <=" (dx-test--goals))))))

(provide 'test-dx-mode)
;;; test-dx-mode.el ends here
