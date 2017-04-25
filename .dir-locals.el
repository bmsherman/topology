;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

((coq-mode
  (coq-indent-proofstart . 0)
  (coq-smie-after-bolp-indentation . 0)
  (company-coq-dir-local-symbols . (("~>" . ?↝) ("<|" . ?◁)))
  . ((eval . (let* ((project-root (locate-dominating-file buffer-file-name "_CoqProject"))
		    (dependencies-folder (expand-file-name "dependencies" project-root))
		    (coq-path (split-string (or (getenv "COQPATH") "") ":" t)))
	       (unless (memql dependencies-folder coq-path)
		 (setenv "COQPATH" (mapconcat #'identity (cons dependencies-folder coq-path) ":"))))))))
