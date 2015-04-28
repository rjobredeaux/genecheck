(in-package :pvs)

(defun generate-mapped-axiom-tccs (modinst)
  ;; Don't try to generate if in prover/evaluator, as there are problems
  ;; if there are decl-formals in any axiom, and we want to treat them uniformly
  (unless (or *in-checker* *in-evaluator*)
    (let ((mod (get-theory modinst)))
      (unless (and (not *collecting-tccs*)
		   (eq mod (current-theory)))
	(let ((prev (find modinst (assuming-instances (current-theory))
			  :test #'(lambda (x y)
				    (not (eq (simple-match (car y) x) 'fail))))))
	  (if prev
	      (let ((aprev (or (cadr prev) (car prev))))
		(pvs-info "Mapped axiom TCCs not generated for~%  ~w~%~
                         as they are subsumed by the TCCs generated for~%  ~w"
		  modinst (place-string aprev) aprev))
	      (let* ((*old-tcc-name* nil))
		;; Don't want to save this module instance unless it does not
		;; depend on any conditions, including implicit ones in the
		;; prover
		(unless (or *collecting-tccs*
			    (some #'(lambda (tcc-cond)
				      (not (typep tcc-cond '(or bind-decl list))))
				  *tcc-conditions*))
		  (push (list modinst nil (current-declaration))
			(assuming-instances (current-theory))))
		(dolist (axiom (collect-mapping-axioms modinst mod))
		  (multiple-value-bind (ndecl mappings-alist)
		      (make-mapped-axiom-tcc-decl axiom modinst mod)
		    (let ((netype (when ndecl (nonempty-formula-type ndecl))))
		      (if (and ndecl
			       (or (null netype)
				   (possibly-empty-type? netype)))
			  (let ((unint (find-uninterpreted
					(definition ndecl)
					modinst mod mappings-alist)))
			    (if unint
				(unless *collecting-tccs*
				  (pvs-warning
				      "Axiom ~a is not a TCC because~%  ~?~% ~
                                     ~:[is~;are~] not interpreted."
				    (id axiom) *andusingctl* unint (cdr unint)))
				(insert-tcc-decl 'mapped-axiom modinst axiom ndecl)))
			  (if ndecl
			      (add-tcc-comment
			       'mapped-axiom nil modinst
			       (cons 'map-to-nonempty 
				     (format nil
					 "%~a~%  % was not generated because ~a is non-empty"
				       (unpindent ndecl 2 :string t :comment? t)
				       (unpindent netype 2 :string t :comment? t))))
			      (add-tcc-comment
			       'mapped-axiom nil modinst)))))))))))))

(defun unparse (obj &key string stream file char-width
		    length level lines (pretty t) no-newlines?)
   (let ((*print-length* length)
	 (*print-level* level)
	 (*print-lines* lines)
	 (*print-pretty* pretty)
	 (*print-escape* nil)
	 (*print-readably* nil)
	 (*print-miser-width* 20) ; Normally 40, less is less likely to becomes miserly
	 (*print-right-margin* (or char-width *default-char-width*))
	 (*pp-no-newlines?* no-newlines?))
     (cond (string
	    (decf *print-right-margin* 4)
	    (with-output-to-string (*standard-output*)
	      (pp obj)))
	   (stream
	    (let ((*standard-output* stream))
	      (pp obj)))
	   (file
	    (with-open-file (*standard-output* file :direction :output)
	      (pp obj)))
	   (t (decf *print-right-margin* 4)
	      (pp obj)))))

(defmethod pp* ((ex infix-implication))
  (let ((impls (collect-infix-impls ex)))
    (if (<= (length impls) 4)
	(call-next-method)
	(pprint-logical-block (nil impls)
	  (write "    ")
	  (loop (pp* (pprint-pop))
		(pprint-exit-if-list-exhausted)
		(pprint-newline :fill)
		(write " => "))))))

(defmethod collect-infix-impls ((ex infix-implication))
  (cons (args1 ex) (collect-infix-impls (args2 ex))))

(defmethod collect-infix-impls (ex)
  (list ex))

(defmethod pp* ((ex let-expr))
  (if (lambda-expr? (operator ex))
      (multiple-value-bind (let-bindings expr)
	  (get-let-bindings ex)
	(pprint-logical-block (nil nil)
	  (write 'LET)
	  (write-char #\space)
	  (pp-let-bindings let-bindings)
	  (write-char #\space)
	  (unless (let-expr? expr)
	    (pprint-indent :block 2))
	  (pprint-newline :fill)
	  (write 'IN)
	  (write-char #\space)
	  (pprint-newline :fill)
	  (pp* expr)))
      (call-next-method)))
