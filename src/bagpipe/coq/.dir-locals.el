((coq-mode . ((eval .
  (let ((root (replace-regexp-in-string "^/\\(\\(ssh\\|docker\\):[^:|]+[:|]\\)+" ""
                (file-name-directory
                  (let ((d (dir-locals-find-file ".")))
                    (if (stringp d) d (car d)))))))
    (set (make-local-variable 'coq-prog-name) "/root/.opam/4.01.0/bin/coqtop")
    (set (make-local-variable 'coq-prog-args) (list
      "-emacs-U" "-R" (expand-file-name "build" root) "Bagpipe")))))))
