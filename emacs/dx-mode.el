;;; dx-mode.el --- Proof General style mode for calculus-checker .dx files -*- lexical-binding: t; -*-

;; Requires Emacs 28 or later.  See app/DX.md in the repository.

;;; Commentary:

;; A .dx file is a tactic script (app/SCRIPT.md) whose first sentence names
;; the goal: `problem ID.' or `goal G [functions f/1, ...].'.  This mode
;; steps through it against the checker's REPL (`./calc --repl'), as
;; Proof General does with Rocq: the checked sentences form a locked
;; region at the top of the buffer, the goal is shown in *dx-goals* and
;; the last answer in *dx-response*.
;;
;; Untrusted, like all of the app: every verdict shown is a string the
;; kernel produced.
;;
;; Keys:
;;   C-c C-n, M-<down>   check the next sentence
;;   C-c C-u, M-<up>     retract the last checked sentence
;;   C-c RET             check or retract up to point
;;   C-c C-b             check to the end of the buffer
;;   C-c C-r             retract everything
;;   C-c C-.             go to the end of the locked region
;;   C-c C-c             stop the running step
;;   C-c C-a             use the last refusal's suggestion
;;   C-c C-t             the next hint rung (a numeric prefix picks it)
;;   C-c C-l             show the goals and response windows
;;   C-c C-p             toggle the pretty display
;;   C-c C-x             stop the checker
;;   C-c TAB             complete a move name into its template

;;; Code:

(require 'json)
(require 'subr-x)
(require 'seq)

(defgroup dx nil
  "Stepping through calculus-checker .dx scripts."
  :group 'languages
  :prefix "dx-")

(defconst dx--here
  (file-name-directory (or load-file-name buffer-file-name default-directory))
  "The directory this file was loaded from.")

(defcustom dx-calc-program
  (let ((local (expand-file-name "../calc" dx--here)))
    (if (file-executable-p local) local "calc"))
  "The checker to run: the repository's ./calc by default."
  :type 'string)

(defcustom dx-calc-args '("--repl")
  "Arguments for `dx-calc-program'."
  :type '(repeat string))

(defcustom dx-pretty t
  "Non-nil turns on the pretty display (`prettify-symbols-mode')."
  :type 'boolean)

(defcustom dx-auto-layout t
  "Non-nil shows the goals and response windows when checking starts."
  :type 'boolean)

(defface dx-locked-face
  '((((background dark)) :background "#1f3a2a" :extend t)
    (t :background "#dcefe2" :extend t))
  "The checked sentences.")

(defface dx-pending-face
  '((((background dark)) :background "#3d3418")
    (t :background "#fdf0c9"))
  "A sentence being checked, or queued.")

(defface dx-error-face
  '((t :underline (:style wave :color "#b3261e")))
  "A refused sentence.")

(defface dx-timeout-face
  '((t :underline (:style line :color "#8a5a00")))
  "A sentence stopped by the timeout or by C-c C-c.")

(defconst dx-moves
  '("ftc" "int_improper" "close" "rewrite" "fact" "int_subst" "int_flip"
    "int_parts" "taylor_lagrange" "bound")
  "The moves, as app/SCRIPT.md names them.")

(defconst dx-templates
  '(("ftc" . "ftc _ by ring.")
    ("int_improper" . "int_improper _ by field.")
    ("close" . "close _ by ring.")
    ("rewrite" . "rewrite entry at _.")
    ("fact" . "fact h := entry with a := _.")
    ("int_subst" . "int_subst x := _ as t from _ to _ by ring.")
    ("int_flip" . "int_flip.")
    ("int_parts" . "int_parts in x with u := _; v := _ by ring.")
    ("taylor_lagrange" . "taylor_lagrange h := lower of _ in u from _ to _ at _ derivs _; _ increasing by field.")
    ("bound" . "bound by field using h."))
  "Each move's shape, as script.TEMPLATES has it (app/PRETTY.md).")

(defconst dx-pretty-symbols
  (append
   '(("Int" . ?∫) ("sqrt" . ?√) ("pi" . ?π) ("oo" . ?∞) ("<=" . ?≤)
     (">=" . ?≥) ("==" . ?≐) (":=" . ?≔) ("->" . ?→) ("/\\" . ?∧))
   (mapcar (lambda (g) (cons (car g) (cdr g)))
           '(("alpha" . ?α) ("beta" . ?β) ("gamma" . ?γ) ("delta" . ?δ)
             ("epsilon" . ?ε) ("zeta" . ?ζ) ("eta" . ?η) ("theta" . ?θ)
             ("iota" . ?ι) ("kappa" . ?κ) ("lambda" . ?λ) ("mu" . ?μ)
             ("nu" . ?ν) ("xi" . ?ξ) ("rho" . ?ρ) ("sigma" . ?σ)
             ("tau" . ?τ) ("upsilon" . ?υ) ("phi" . ?φ) ("chi" . ?χ)
             ("psi" . ?ψ) ("omega" . ?ω))))
  "What the pretty display draws in place of the grammar's words.
Only the drawing changes: the buffer, what is saved and what is sent stay
plain text (app/DX.md).  `*' is left alone: it would draw `(*' as `(·'.")

;;;; Buffer state

(defvar-local dx--proc nil "The checker process for this buffer.")
(defvar-local dx--session nil "The API session, once the header is checked.")
(defvar-local dx--path nil "Node ids: element k is the node after sentence k.")
(defvar-local dx--done nil "Checked sentences, as (START . END) markers, in order.")
(defvar-local dx--queue nil "Sentences waiting to be checked, as marker pairs.")
(defvar-local dx--busy nil "The id of the request in flight, or nil.")
(defvar-local dx--locked-ov nil)
(defvar-local dx--pending-ov nil)
(defvar-local dx--error-ov nil)
(defvar-local dx--last-refusal nil "(SUGGESTION . ERROR-OVERLAY) of the last refusal.")
(defvar-local dx--hint nil "(NODE . RUNG) of the last hint.")
(defvar-local dx--partial "" "Output not yet ended by a newline.")
(defvar-local dx--callbacks nil "Alist of request id to callback.")
(defvar-local dx--next-id 0)

;;;; Sentences (app/SCRIPT.md, the same rule as script.next_sentence)

(defconst dx--space '(?\s ?\t ?\n ?\r ?\f ?\v)
  "ASCII whitespace only, as the Python and JavaScript splitters use.")

(defun dx--next-sentence (from)
  "The (START . END) of the first sentence at or after FROM, or nil.
A sentence ends at a `.' followed by whitespace or the end, outside
\(* *) comments (which do not nest), never inside `..'."
  (save-excursion
    (let ((i from) (start nil) (limit (point-max)) (found nil) (stop nil))
      (while (and (not stop) (< i limit))
        (cond
         ((and (eq (char-after i) ?\() (eq (char-after (1+ i)) ?*))
          (goto-char (+ i 2))
          (if (search-forward "*)" nil t)
              (setq i (point))
            (setq stop t)))
         (t
          (let ((c (char-after i)))
            (unless (or start (memq c dx--space))
              (setq start i))
            (when (and (eq c ?.)
                       (not (and (> i (point-min)) (eq (char-before i) ?.)))
                       (not (eq (char-after (1+ i)) ?.))
                       (or (= (1+ i) limit) (memq (char-after (1+ i)) dx--space)))
              (setq found (and start (cons start (1+ i))) stop t))
            (setq i (1+ i))))))
      found)))

(defun dx--locked-end ()
  "Where the locked region ends."
  (if dx--done (marker-position (cdar (last dx--done))) (point-min)))

(defun dx--span-text (span)
  (buffer-substring-no-properties (car span) (cdr span)))

;;;; The process

(defun dx--start ()
  "Start the checker for this buffer, unless it runs."
  (unless (process-live-p dx--proc)
    (let ((buf (current-buffer))
          (process-connection-type nil))
      (setq dx--partial "" dx--callbacks nil)
      (setq dx--proc
            (make-process
             :name "dx-calc"
             :buffer nil
             :command (cons dx-calc-program dx-calc-args)
             :connection-type 'pipe
             :coding 'utf-8
             :noquery t
             :filter (lambda (_p out)
                       (when (buffer-live-p buf)
                         (with-current-buffer buf (dx--filter out))))
             :sentinel (lambda (_p event)
                         (when (buffer-live-p buf)
                           (with-current-buffer buf (dx--died event))))))
      (when (and dx-auto-layout (not noninteractive)) (dx-layout)))))

(defun dx--died (event)
  (unless (process-live-p dx--proc)
    (dx--reset)
    (dx--show-response (format "The checker stopped: %s" (string-trim event)))))

(defun dx--filter (out)
  (setq dx--partial (concat dx--partial out))
  (let ((lines (split-string dx--partial "\n")))
    (setq dx--partial (car (last lines)))
    (dolist (line (butlast lines))
      (unless (string-empty-p (string-trim line))
        (let* ((msg (json-parse-string line :object-type 'alist
                                       :array-type 'list :null-object nil
                                       :false-object nil))
               (id (alist-get 'id msg))
               (cb (and id (alist-get id dx--callbacks))))
          (when cb
            (setq dx--callbacks (assq-delete-all id dx--callbacks))
            (funcall cb (alist-get 'status msg) (alist-get 'body msg))))))))

(defun dx--request (method path body callback)
  "Send one request; CALLBACK gets the status and the body.  Returns its id."
  (dx--start)
  (let ((id (setq dx--next-id (1+ dx--next-id))))
    (push (cons id callback) dx--callbacks)
    (process-send-string
     dx--proc
     (concat (json-serialize `((id . ,id) (method . ,method) (path . ,path)
                               (body . ,body)))
             "\n"))
    id))

;;;; Overlays and the read-only lock

(defun dx--overlay (sym start end face)
  "Put the overlay held in SYM on START..END with FACE."
  (let ((ov (symbol-value sym)))
    (if (overlayp ov) (move-overlay ov start end)
      (setq ov (make-overlay start end nil nil nil))
      (set sym ov))
    (overlay-put ov 'face face)
    ov))

(defun dx--paint ()
  (dx--overlay 'dx--locked-ov (point-min) (dx--locked-end) 'dx-locked-face)
  (if dx--queue
      (dx--overlay 'dx--pending-ov (car (car dx--queue))
                   (cdr (car (last dx--queue))) 'dx-pending-face)
    (when (overlayp dx--pending-ov) (delete-overlay dx--pending-ov)
          (setq dx--pending-ov nil))))

(defun dx--lock (on)
  "While a request runs the locked and queued text is read-only (DX.md
review 2): a text property, so no change hook ever has to signal."
  (with-silent-modifications
    (let ((end (max (dx--locked-end)
                    (if dx--queue (cdr (car (last dx--queue))) (point-min)))))
      (if on
          (add-text-properties (point-min) end
                               '(read-only "busy: wait, or C-c C-c"
                                 front-sticky (read-only)))
        (remove-text-properties (point-min) (point-max)
                                '(read-only nil front-sticky nil))))))

(defun dx--clear-error ()
  (when (overlayp dx--error-ov) (delete-overlay dx--error-ov))
  (setq dx--error-ov nil))

;;;; Stepping

(defun dx--reset ()
  "Forget the session: nothing is locked."
  (setq dx--session nil dx--path nil dx--done nil dx--queue nil dx--busy nil
        dx--hint nil)
  (dx--lock nil)
  (dx--clear-error)
  (dx--paint))

(defun dx--enqueue-until (limit)
  "Queue every sentence after the locked region that starts before LIMIT."
  (let ((at (if dx--queue (cdr (car (last dx--queue))) (dx--locked-end)))
        s)
    (while (and (setq s (dx--next-sentence at)) (< (car s) limit))
      (setq dx--queue (append dx--queue
                              (list (cons (copy-marker (car s))
                                          (copy-marker (cdr s))))))
      (setq at (cdr s)))))

(defun dx--run ()
  "Check the next queued sentence, if nothing runs."
  (when (and dx--queue (not dx--busy))
    (dx--clear-error)
    (dx--paint)
    (let* ((span (car dx--queue))
           (text (dx--span-text span))
           (buf (current-buffer))
           (done (lambda (status body)
                   (when (buffer-live-p buf)
                     (with-current-buffer buf
                       (dx--answer span status body))))))
      (dx--lock t)
      (setq dx--busy
            (if (null dx--done)
                (dx--request "POST" "/session" `((header . ,text)) done)
              (dx--request "POST" "/tactic"
                           `((session . ,dx--session)
                             (node . ,(car (last dx--path)))
                             (text . ,text))
                           done))))))

(defun dx--stop-queue (span face)
  "Stop at SPAN, marked with FACE; nothing more runs."
  (setq dx--queue nil)
  (dx--overlay 'dx--error-ov (car span) (cdr span) face))

(defun dx--answer (span status body)
  (setq dx--busy nil)
  (dx--lock nil)
  (setq dx--queue (cdr dx--queue))
  (let ((refusal (alist-get 'refusal body))
        (timeout (alist-get 'timeout body))
        (err (alist-get 'error body)))
    (cond
     ((or err (not (eql status 200)))
      (dx--stop-queue span 'dx-error-face)
      (dx--show-response
       (format "%s: %s" (alist-get 'code err) (alist-get 'message err))))
     (refusal
      (dx--stop-queue span 'dx-error-face)
      (let ((st (alist-get 'stuck refusal)))
        (setq dx--last-refusal
              (and st (alist-get 'suggest st)
                   (cons (string-join (alist-get 'suggest st) "\n")
                         dx--error-ov))))
      (dx--show-refusal refusal))
     (timeout
      (dx--stop-queue span 'dx-timeout-face)
      (dx--show-response (alist-get 'message timeout)))
     (t
      (when (null dx--done)
        (setq dx--session (alist-get 'session body)))
      (setq dx--path (append dx--path (list (alist-get 'node body))))
      (setq dx--done (append dx--done (list span)))
      (dx--show-node body)
      (dx--show-response
       (if (equal (alist-get 'move body) "install")
           (format "%s: the goal is installed" (alist-get 'node body))
         (let ((new (seq-count (lambda (o) (alist-get 'new o))
                               (alist-get 'obligations body))))
           (format "%s: %s accepted%s" (alist-get 'node body)
                   (alist-get 'move body)
                   (if (> new 0) (format ", %d new obligation(s)" new) "")))))))
    (dx--paint)
    (dx--run)))

(defun dx--retract-to (k)
  "Keep the first K checked sentences.  The locked region shrinks at once;
the /retract goes out afterwards (DX.md review 2)."
  (when (< k (length dx--done))
    (let ((victim (nth k dx--path))
          (session dx--session)
          (buf (current-buffer)))
      (dx--clear-error)
      (setq dx--queue nil)
      (if (= k 0)
          ;; the header: the API keeps n0, so the client drops the session
          (progn (dx--reset)
                 (dx--show-goals "No goal: the header is not checked.")
                 (dx--show-response "Retracted everything."))
        (setq dx--path (seq-take dx--path k)
              dx--done (seq-take dx--done k))
        (dx--paint)
        (dx--request "POST" "/retract" `((session . ,session) (node . ,victim))
                     (lambda (_status body)
                       (when (buffer-live-p buf)
                         (with-current-buffer buf
                           (when (alist-get 'node body)
                             (dx--show-node body)))))))
      (dx--paint))))

(defun dx--sentence-index (pos)
  "The index of the first checked sentence ending after POS."
  (seq-position dx--done pos (lambda (d p) (> (marker-position (cdr d)) p))))

(defun dx--before-change (beg _end)
  "An edit inside the locked region retracts to the sentence edited."
  (when (and dx--done (not dx--busy) (< beg (dx--locked-end)))
    (dx--retract-to (dx--sentence-index beg))))

(defun dx--after-change (beg end len)
  "An insertion right after the last checked `.' that does not start with
whitespace edits that sentence (`close 2.' + `5', DX.md review 2)."
  (when (and dx--done (not dx--busy) (= len 0) (> end beg)
             (= beg (dx--locked-end))
             (not (memq (char-after beg) dx--space)))
    (dx--retract-to (1- (length dx--done)))))

;;;; Commands

(defun dx--check-idle ()
  (when dx--busy (user-error "Busy: wait, or C-c C-c")))

(defun dx-next ()
  "Check the next sentence."
  (interactive)
  (dx--check-idle)
  (let ((s (dx--next-sentence (dx--locked-end))))
    (if (not s) (message "Nothing more to check")
      (dx--enqueue-until (1+ (car s)))
      (dx--run))))

(defun dx-undo ()
  "Retract the last checked sentence."
  (interactive)
  (dx--check-idle)
  (if dx--done (dx--retract-to (1- (length dx--done)))
    (message "Nothing is checked")))

(defun dx-goto-point ()
  "Check or retract up to point."
  (interactive)
  (dx--check-idle)
  (if (< (point) (dx--locked-end))
      (dx--retract-to (dx--sentence-index (point)))
    (dx--enqueue-until (point))
    (dx--run)))

(defun dx-goto-end ()
  "Check to the end of the buffer."
  (interactive)
  (dx--check-idle)
  (dx--enqueue-until (point-max))
  (dx--run))

(defun dx-retract-all ()
  "Retract everything, the header too."
  (interactive)
  (dx--check-idle)
  (when dx--done (dx--retract-to 0)))

(defun dx-goto-locked-end ()
  "Move point to the end of the locked region."
  (interactive)
  (goto-char (dx--locked-end)))

(defun dx-interrupt ()
  "Stop the running step: nothing changes, and it is not refused."
  (interactive)
  (if (not (and dx--busy (process-live-p dx--proc)))
      (message "Nothing is running")
    (process-send-string
     dx--proc (concat (json-serialize `((id . 0) (path . "/cancel")
                                        (body . ((id . ,dx--busy)))))
                      "\n"))))

(defun dx-use-suggestion ()
  "Put the last refusal's suggestion in place of the refused sentence."
  (interactive)
  (dx--check-idle)
  (let ((sug (car dx--last-refusal)) (ov (cdr dx--last-refusal)))
    (if (not (and sug (overlayp ov) (overlay-buffer ov)))
        (message "No suggestion to use")
      (let ((start (overlay-start ov)) (end (overlay-end ov)))
        (dx--clear-error)
        (setq dx--last-refusal nil)
        (save-excursion
          (goto-char start)
          (delete-region start end)
          (insert sug))))))

(defun dx-hint (&optional rung)
  "Ask for a hint on the current node: the next rung, or RUNG (1 to 3)."
  (interactive "P")
  (dx--check-idle)
  (unless dx--session (user-error "Check the header first"))
  (let* ((node (car (last dx--path)))
         (r (cond (rung (max 1 (min 3 (prefix-numeric-value rung))))
                  ((equal (car dx--hint) node) (min 3 (1+ (cdr dx--hint))))
                  (t 1)))
         (buf (current-buffer)))
    (setq dx--hint (cons node r))
    (dx--request "GET" "/hint" `((session . ,dx--session) (node . ,node)
                                 (rung . ,(number-to-string r)))
                 (lambda (_status body)
                   (when (buffer-live-p buf)
                     (with-current-buffer buf
                       (let ((ref (alist-get 'refusal body)))
                         (dx--show-response
                          (if ref (format "%s: %s" (alist-get 'code ref)
                                          (alist-get 'message ref))
                            (format "Hint %s · %s\n%s\nCosts: %s"
                                    (make-string r ??)
                                    (alist-get 'integral body)
                                    (alist-get 'text body)
                                    (alist-get 'cost body)))))))))))

(defun dx-exit ()
  "Stop the checker; the locked region is cleared."
  (interactive)
  (when (process-live-p dx--proc) (delete-process dx--proc))
  (setq dx--proc nil)
  (dx--reset))

(defun dx-complete ()
  "Complete the move name before point into its template (app/PRETTY.md)."
  (interactive)
  (let* ((end (point))
         (start (save-excursion (skip-chars-backward "a-z_") (point)))
         (prefix (buffer-substring-no-properties start end))
         (choice (completing-read "Tactic: " dx-templates nil t prefix)))
    (when-let ((tpl (cdr (assoc choice dx-templates))))
      (delete-region start end)
      (insert tpl)
      (goto-char start)
      (when (search-forward "_" (+ start (length tpl)) t)
        (backward-char)))))

;;;; The goals and response windows

(defun dx--special-buffer (name)
  (let ((buf (get-buffer-create name)))
    (with-current-buffer buf
      (unless (derived-mode-p 'dx-goals-mode) (dx-goals-mode)))
    buf))

(defun dx--show-goals (text)
  (with-current-buffer (dx--special-buffer "*dx-goals*")
    (let ((inhibit-read-only t))
      (erase-buffer)
      (insert text)
      (goto-char (point-min)))))

(defun dx--show-response (text)
  (with-current-buffer (dx--special-buffer "*dx-response*")
    (let ((inhibit-read-only t))
      (erase-buffer)
      (insert (or text ""))
      (goto-char (point-min)))))

(defun dx--show-node (n)
  (dx--show-goals
   (concat
    (alist-get 'report n) "\n"
    (when (alist-get 'goal n) (format "\nGoal\n  %s\n" (alist-get 'goal n)))
    (when (alist-get 'theorem n)
      (format "\nTheorem\n  %s\n" (alist-get 'theorem n)))
    (when (alist-get 'handles n)
      (format "\nFacts: %s\n" (string-join (alist-get 'handles n) ", ")))
    (let ((obs (alist-get 'obligations n)))
      (format "\nObligations (%d)\n%s" (length obs)
              (mapconcat
               (lambda (o)
                 (format "  %-10s %s%s  [%s]"
                         (alist-get 'status o) (alist-get 'key o)
                         (if (alist-get 'new o) " (new)" "")
                         (string-join (delq nil (cons (alist-get 'method o)
                                                      (alist-get 'cites o)))
                                      ", ")))
               obs "\n"))))))

(defun dx--show-refusal (r)
  (let ((st (alist-get 'stuck r)))
    (dx--show-response
     (concat
      (format "%s: %s\n" (alist-get 'code r) (alist-get 'message r))
      (when (alist-get 'residual r)
        (format "residual: %s\n" (alist-get 'residual r)))
      (when st
        (concat "\n" (upcase (or (cdr (assoc (alist-get 'kind st)
                                              '(("no-match" . "nothing matches")
                                                ("obligation" . "a condition fails")
                                                ("algebra" . "the algebra does not close"))))
                                 "refused"))
                "\n" (alist-get 'headline st) "\n"
                (mapconcat (lambda (l) (concat " - " l "\n"))
                           (alist-get 'lines st) "")
                (when (alist-get 'suggest st)
                  (concat "\nSuggestion (C-c C-a):\n  "
                          (string-join (alist-get 'suggest st) "\n  ")
                          "\n"))))))))

(defun dx-layout ()
  "Show the script, the goals and the response side by side."
  (interactive)
  (let ((script (current-buffer)))
    (delete-other-windows)
    (let* ((right (split-window-right))
           (below (with-selected-window right (split-window-below))))
      (set-window-buffer right (dx--special-buffer "*dx-goals*"))
      (set-window-buffer below (dx--special-buffer "*dx-response*"))
      (switch-to-buffer script))))

;;;; Modes

(defvar dx-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; (* comments *), which do not nest (no `n' flag), as the splitters say
    (modify-syntax-entry ?\( "()1" st)
    (modify-syntax-entry ?* ". 23" st)
    (modify-syntax-entry ?\) ")(4" st)
    (modify-syntax-entry ?_ "_" st)
    (modify-syntax-entry ?' "_" st)
    (dolist (c '(?+ ?- ?/ ?^ ?= ?< ?> ?# ?@ ?: ?\;))
      (modify-syntax-entry c "." st))
    st)
  "Syntax table for `dx-mode'.")

(defconst dx-font-lock-keywords
  `((,(regexp-opt '("problem" "goal" "functions") 'symbols)
     . font-lock-preprocessor-face)
    (,(regexp-opt dx-moves 'symbols) . font-lock-keyword-face)
    (,(regexp-opt '("by" "using" "with" "at" "occurrence" "as" "from" "to"
                    "reverse" "in" "derivs" "increasing" "decreasing"
                    "lower" "upper" "of")
                  'symbols)
     . font-lock-builtin-face)
    (,(regexp-opt '("ring" "field") 'symbols) . font-lock-constant-face)
    ("\\_<rewrite\\s-+\\(\\(?:\\sw\\|\\s_\\)+\\)" 1 font-lock-function-name-face)
    ("\\_<fact\\s-+\\(?:\\sw\\|\\s_\\)+\\s-*:=\\s-*\\(\\(?:\\sw\\|\\s_\\)+\\)"
     1 font-lock-function-name-face)
    (,(regexp-opt '("Int" "D" "sqrt" "sin" "cos" "tan" "asin" "acos" "atan"
                    "exp" "ln" "abs" "sinh" "cosh" "tanh" "asinh" "acosh"
                    "atanh" "pi" "oo" "e_const")
                  'symbols)
     . font-lock-type-face))
  "Highlighting for `dx-mode'.")

(defvar dx-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "C-c C-n") #'dx-next)
    (define-key m (kbd "M-<down>") #'dx-next)
    (define-key m (kbd "C-c C-u") #'dx-undo)
    (define-key m (kbd "M-<up>") #'dx-undo)
    (define-key m (kbd "C-c RET") #'dx-goto-point)
    (define-key m (kbd "C-c C-b") #'dx-goto-end)
    (define-key m (kbd "C-c C-r") #'dx-retract-all)
    (define-key m (kbd "C-c C-.") #'dx-goto-locked-end)
    (define-key m (kbd "C-c C-c") #'dx-interrupt)
    (define-key m (kbd "C-c C-a") #'dx-use-suggestion)
    (define-key m (kbd "C-c C-t") #'dx-hint)
    (define-key m (kbd "C-c C-l") #'dx-layout)
    (define-key m (kbd "C-c C-p") #'prettify-symbols-mode)
    (define-key m (kbd "C-c C-x") #'dx-exit)
    (define-key m (kbd "C-c TAB") #'dx-complete)
    m)
  "Keys for `dx-mode'.")

(defun dx--pretty-setup ()
  (setq-local prettify-symbols-alist dx-pretty-symbols)
  (setq-local prettify-symbols-unprettify-at-point 'right-edge)
  (when dx-pretty (prettify-symbols-mode 1)))

;;;###autoload
(define-derived-mode dx-mode prog-mode "dx"
  "Step through a calculus-checker .dx script, Proof General style.

\\{dx-mode-map}"
  :syntax-table dx-mode-syntax-table
  (setq-local comment-start "(* ")
  (setq-local comment-end " *)")
  (setq-local comment-start-skip "(\\*+\\s-*")
  (setq-local font-lock-defaults '(dx-font-lock-keywords))
  (dx--pretty-setup)
  (add-hook 'before-change-functions #'dx--before-change nil t)
  (add-hook 'after-change-functions #'dx--after-change nil t)
  (add-hook 'kill-buffer-hook #'dx-exit nil t))

(define-derived-mode dx-goals-mode special-mode "dx-goals"
  "The goals and responses of a `dx-mode' buffer."
  (setq-local font-lock-defaults '(dx-font-lock-keywords))
  (dx--pretty-setup))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.dx\\'" . dx-mode))

(provide 'dx-mode)
;;; dx-mode.el ends here
