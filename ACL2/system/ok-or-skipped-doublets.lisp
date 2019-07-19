; This

(in-package "ACL2")

(program)
(set-state-ok t)

(defun skip-proofs-event-names (wrld acc)
  (cond ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value)
              (equal (access-event-tuple-form (cddar wrld))
                     '(exit-boot-strap-mode)))
         acc)
        (t
         (let ((namex (and (eq (caar wrld) 'event-landmark)
                           (eq (cadar wrld) 'global-value)
                           (access-event-tuple-skipped-proofs-p (cddar wrld))
                           (access-event-tuple-namex (cddar wrld)))))
           (skip-proofs-event-names
            (cdr wrld)
            (cond ((null namex) acc)
                  ((symbolp namex) (cons namex acc))
                  ((symbol-listp namex) (append namex acc))
                  (t acc)))))))

(defun ok-or-skipped-doublets-1 (names all-skipped-names acc)
  (cond ((endp names) (reverse acc))
        (t (ok-or-skipped-doublets-1
            (cdr names)
            all-skipped-names
            (cons (list (car names)
                        (if (member-eq (car names) all-skipped-names)
                            'skipped
                          'ok))
                  acc)))))

(defun ok-or-skipped-doublets (names wrld)
  (let* ((all-skipped-names (skip-proofs-event-names wrld nil))
         (extra-names (set-difference-eq all-skipped-names names)))
    (mv (ok-or-skipped-doublets-1 names all-skipped-names nil)
        extra-names)))

(defun set-current-package-state (val state)
  (mv-let (erp ans state)
    (set-current-package val state)
    (declare (ignore erp ans))
    state))

(defun print-ok-or-skipped-doublets-aux (names state)
  (state-global-let*
   ((fmt-soft-right-margin 100000 set-fmt-soft-right-margin)
    (fmt-hard-right-margin 100000 set-fmt-hard-right-margin)
    (current-package "ACL2" set-current-package-state))
   (mv-let (doublets extra)
     (ok-or-skipped-doublets names (w state))
     (mv-let (col state)
       (fmx "~%~%CHECK-RESULT: list of pairs: ~x0~|~%" doublets)
       (declare (ignore col))
       (cond
        (extra (mv-let (col state)
                 (fmx "~%~%CHECK-RESULT: list of other skipped events: ~x0~|~%"
                      extra)
                 (declare (ignore col))
                 (value :invisible)))
        (t (value :invisible)))))))

(defun print-ok-or-skipped-doublets-fn (names)
  `(make-event (er-progn (print-ok-or-skipped-doublets-aux ',names state)
                         (value '(value-triple :CHECK-COMPLETED)))))

(defmacro print-ok-or-skipped-doublets (&rest names)

; Returns (mv alist lst), where (strip-cars alist) is names and each name is
; paired with t or nil depending on whether name is the name of

  (print-ok-or-skipped-doublets-fn names))
