;;; lang/dx/config.el -*- lexical-binding: t; -*-

(defvar +dx-dir
  ;; The module is emacs/doom/dx in the checkout, usually linked into
  ;; $DOOMDIR/modules/lang/dx: its real directory's ../.. is emacs/.
  (file-name-as-directory (expand-file-name "../.." (file-truename (dir!))))
  "The checkout's emacs/ directory, which holds dx-mode.el.
Set it in $DOOMDIR/init.el, before `doom!', if the module was copied
rather than linked.")

(defvar +dx-eglot-auto t
  "Non-nil connects a .dx buffer to the checker when it is opened.
The module's stand-in for `dx-eglot-auto', which it turns off.")

(defvar +dx-file-template
  "goal ${1:Int[x = 0 .. 1] 3*x^2 + 2*x} == ?A.\n$0"
  "What a new .dx file starts with, as a yasnippet body.")

(unless (file-exists-p (expand-file-name "dx-mode.el" +dx-dir))
  (warn "lang/dx: no dx-mode.el in `+dx-dir' (%s). Link the module from \
the checkout, or set `+dx-dir' in init.el before `doom!'" +dx-dir))


;;
;;; Commands
;; Here rather than in autoload.el: Doom does not index the autoloads of a
;; module linked into $DOOMDIR/modules, and linking is how this one is used.

(defun +dx/layout ()
  "Show *dx-goals* and *dx-response* beside the script: as popups with
:ui popup, else as dx-mode's own side-by-side layout."
  (interactive)
  (if (not (modulep! :ui popup))
      (dx-layout)
    (let ((script (selected-window)))
      (dolist (name '("*dx-goals*" "*dx-response*"))
        (display-buffer (dx--special-buffer name)))
      (select-window script)
      (setq dx--goals-at nil)
      (dx--goals-refresh))))

(defun +dx/goals ()
  "Show the goal at point in *dx-goals*."
  (interactive)
  (display-buffer (dx--special-buffer "*dx-goals*"))
  (setq dx--goals-at nil)
  (dx--goals-refresh))

(defun +dx/evaluate-and-insert ()
  "Evaluate the integral goal at point and insert its checked proof there."
  (interactive)
  (display-buffer (dx--special-buffer "*dx-response*"))
  (dx-evaluate '(4)))

(defun +dx-eglot-ensure-h ()
  (when +dx-eglot-auto (eglot-ensure)))

(defun +dx-snippet-body (template)
  "TEMPLATE, a move's shape from `dx-templates', as a yasnippet body.
Each `_' becomes a field in order; point ends after the sentence."
  (let ((n 0))
    (concat (replace-regexp-in-string
             "_" (lambda (_) (format "${%d:_}" (cl-incf n))) template t t)
            "$0")))

(defun +dx-define-snippets-h ()
  "Define a snippet for each move in `dx-templates'."
  (yas-define-snippets
   'dx-mode
   (mapcar (lambda (entry)
             (list (car entry) (+dx-snippet-body (cdr entry)) (car entry)))
           dx-templates)))

(defun +dx-insert-file-template ()
  "Start a new .dx file from `+dx-file-template'."
  (require 'yasnippet)
  (yas-minor-mode-on)
  (yas-expand-snippet +dx-file-template)
  (when (bound-and-true-p evil-local-mode) (evil-insert-state)))


;;
;;; Packages

;; At top level, not in :config, so that the user's own rules, which run
;; later, take precedence.
(set-popup-rules!
  '(("^\\*dx-goals\\*"    :side right :size 0.45 :slot 0 :vslot 0
     :select nil :quit nil :ttl nil :modeline t)
    ("^\\*dx-response\\*" :side right :size 0.45 :slot 1 :vslot 0
     :select nil :quit nil :ttl nil :modeline t)))

(set-file-template! 'dx-mode :trigger #'+dx-insert-file-template)

(use-package! dx-mode
  :load-path +dx-dir
  :mode ("\\.dx\\'" . dx-mode)
  :init
  ;; Connect from `dx-mode-local-vars-hook', like Doom's `lsp!': it skips
  ;; previews and temporary buffers, which the mode body would connect.
  (setq dx-eglot-auto nil)
  (add-hook 'dx-mode-local-vars-hook #'+dx-eglot-ensure-h)

  :config
  (define-key dx-mode-map [remap dx-layout] #'+dx/layout)

  (map! :map dx-mode-map
        :localleader
        "l" #'+dx/layout
        "g" #'+dx/goals
        "h" #'dx-hint
        "a" #'dx-use-suggestion
        "e" #'dx-evaluate
        "E" #'+dx/evaluate-and-insert
        "c" #'dx-complete
        "p" #'prettify-symbols-mode))


(after! (:and yasnippet dx-mode)
  (+dx-define-snippets-h)
  ;; `yas-reload-all' (as `doom/reload' runs it) empties the tables
  (add-hook 'yas-after-reload-hook #'+dx-define-snippets-h))
