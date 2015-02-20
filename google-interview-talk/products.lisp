(defun foo (a)
  (let ((r (make-array (length a))))
    (loop for p = 1 then (* p (aref a i))
          for i from 0 below (length a)
          do (setf (aref r i) p))
    (loop for p = 1 then (* p (aref a i))
          for i from (1- (length a)) downto 0
          do (setf (aref r i) (* (aref r i) p)))
    r))
