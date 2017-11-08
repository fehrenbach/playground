;; function clz3(x)
    ;; if x = 0 return 32
    ;; n ← 0
    ;; if (x & 0xFFFF0000) = 0: n ← n + 16, x ← x << 16
    ;; if (x & 0xFF000000) = 0: n ← n +  8, x ← x <<  8
    ;; if (x & 0xF0000000) = 0: n ← n +  4, x ← x <<  4
    ;; if (x & 0xC0000000) = 0: n ← n +  2, x ← x <<  2
    ;; if (x & 0x80000000) = 0: n ← n +  1
;; return n
(declaim (inline clz-binary))
(defun clz-binary (x)
  "count leading zeroes with binary search on an unsigned byte"
  (declare (type (unsigned-byte 8) x))
  (declare (optimize (safety 0) (speed 3)))
  (the (unsigned-byte 8)
    (if (= x 0) 8
      (let ((n 0))
        (declare (type (unsigned-byte 8) n))
        (when (= (logand x #xF0) 0)
          (setf n (+ n 4) x (ash x 4)))
        (when (= (logand x #xC0) 0)
          (setf n (+ n 2) x (ash x 2)))
        (when (= (logand x #x80) 0)
          (setf n (+ n 1)))
        n))))

(declaim (inline clz))
(defun clz (x)
  (declare (type (unsigned-byte 8) x))
  (declare (optimize (safety 0) (speed 3)))
  (the (unsigned-byte 8) (- 8 (integer-length x))))

(defun foo (b p)
  (declare (type (unsigned-byte 8) b p))
  (declare (optimize (safety 0) (speed 3)))
  ;; Set first p bits in b to 0
  (setf b (logand b (ash 255 (- p))))
  (- (clz-binary b) p))

(defun bar (b p)
  (declare (type (unsigned-byte 8) b p))
  (declare (optimize (safety 0) (speed 3)))
  ;; Set first p bits in b to 0
  (setf b (logand b (ash 255 (- p))))
  (- 8 (integer-length b) p))

;; binary search version:

; disassembly for FOO
; Size: 131 bytes. Origin: #x10022F628F
; 28F:       4881FF80000000   CMP RDI, 128                    ; no-arg-parsing entry point
; 296:       7D76             JNL L9
; 298:       488BCF           MOV RCX, RDI
; 29B:       48D1F9           SAR RCX, 1
; 29E:       BBFE010000       MOV EBX, 510
; 2A3:       48D3FB           SAR RBX, CL
; 2A6:       4883E3FE         AND RBX, -2
; 2AA: L0:   4821D8           AND RAX, RBX
; 2AD:       4885C0           TEST RAX, RAX
; 2B0:       7511             JNE L2
; 2B2:       B810000000       MOV EAX, 16
; 2B7: L1:   4829F8           SUB RAX, RDI
; 2BA:       488BD0           MOV RDX, RAX
; 2BD:       488BE5           MOV RSP, RBP
; 2C0:       F8               CLC
; 2C1:       5D               POP RBP
; 2C2:       C3               RET
; 2C3: L2:   31C9             XOR ECX, ECX
; 2C5:       488BD0           MOV RDX, RAX
; 2C8:       4881E2E0010000   AND RDX, 480
; 2CF:       4885D2           TEST RDX, RDX
; 2D2:       742F             JEQ L8
; 2D4: L3:   488BD0           MOV RDX, RAX
; 2D7:       4881E280010000   AND RDX, 384
; 2DE:       4885D2           TEST RDX, RDX
; 2E1:       7416             JEQ L7
; 2E3: L4:   482500010000     AND RAX, 256
; 2E9:       4885C0           TEST RAX, RAX
; 2EC:       7405             JEQ L6
; 2EE: L5:   488BC1           MOV RAX, RCX
; 2F1:       EBC4             JMP L1
; 2F3: L6:   4883C102         ADD RCX, 2
; 2F7:       EBF5             JMP L5
; 2F9: L7:   4883C104         ADD RCX, 4
; 2FD:       48C1E002         SHL RAX, 2
; 301:       EBE0             JMP L4
; 303: L8:   B908000000       MOV ECX, 8
; 308:       48C1E004         SHL RAX, 4
; 30C:       EBC6             JMP L3
; 30E: L9:   31DB             XOR EBX, EBX
; 310:       EB98             JMP L0


;; integer-length version emits BSR

; disassembly for FOO
; Size: 62 bytes. Origin: #x10046F62DF
; 2DF:       4881FF80000000   CMP RDI, 128                    ; no-arg-parsing entry point
; 2E6:       7D31             JNL L1
; 2E8:       488BCF           MOV RCX, RDI
; 2EB:       48D1F9           SAR RCX, 1
; 2EE:       BBFE010000       MOV EBX, 510
; 2F3:       48D3FB           SAR RBX, CL
; 2F6:       4883E3FE         AND RBX, -2
; 2FA: L0:   4821D8           AND RAX, RBX
; 2FD:       4883C801         OR RAX, 1
; 301:       480FBDC0         BSR RAX, RAX
; 305:       48D1E0           SHL RAX, 1
; 308:       BA10000000       MOV EDX, 16
; 30D:       4829C2           SUB RDX, RAX
; 310:       4829FA           SUB RDX, RDI
; 313:       488BE5           MOV RSP, RBP
; 316:       F8               CLC
; 317:       5D               POP RBP
; 318:       C3               RET
; 319: L1:   31DB             XOR EBX, EBX
; 31B:       EBDD             JMP L0

(defparameter iterations 1000000)

(disassemble #'foo)
(disassemble #'bar)

(print "binary")
(time
 (loop for i from 0 to iterations
       do
       (loop for b from 0 to 255
             do (loop for p from 0 to 8
                      do (foo b p)))))

(print "built-in integer-length/BSR")
(time
 (loop for i from 0 to iterations
       do
       (loop for b from 0 to 255
             do (loop for p from 0 to 8
                      do (bar b p)))))
