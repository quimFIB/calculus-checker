;; -*- no-byte-compile: t; -*-
;;; lang/dx/packages.el

;; Nothing to install.  dx-mode lives in the calculus-checker checkout and is
;; loaded from there (see config.el), because it finds the checker as
;; ../calc next to itself; a copy in straight's build directory would not.
;; eglot is built into Emacs 29 and later; `:tools (lsp +eglot)' pins a
;; newer one, which dx-mode also works with.
