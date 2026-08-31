(IMPLIES
 (AND
  (EQUAL (G :TTYPE INPUT-I) :NORMAL)
 
  (CL-CHECKPOINT-BODY-INPUTS-P (APPEND (CDR PREFIX-INPUTS)
                                       (LIST INPUT-I INPUT-J)))

             NIL))))))))
   (G :PID INPUT-J)))
 (SPEC-LEGAL-INPUTP
     (RUN-SPEC SPEC-START-ST
               (SPEC-COMPATIBLE-INPUT-SEQUENCE IMP-START-ST PREFIX-INPUTS))
     (SPEC-COMPATIBLE-INPUT INPUT-J
                            (STEP-NORMAL (RUN-IMP IMP-START-ST PREFIX-INPUTS)
                                         (G :PID INPUT-I)))))
