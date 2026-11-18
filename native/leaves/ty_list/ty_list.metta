; Construct a type-list row from the live Y identifiers in the operand stack.
; Validate every identifier before checking the storage needed for insertion.
; Plan insertions against the read-only view of the table plus a work log.
; Each 32-byte log entry holds the two key words and its originally empty
; hash slot. The commit writes the proposed rows and slots, then publishes
; the count. Neither a refusal nor a capacity failure writes the table.

!(import! &self "../../p1/p1.metta")

(= (ty_list:first) 0)
(= (ty_list:length) 8)
(= (ty_list:y-count) 16)
(= (ty_list:old-count) 24)
(= (ty_list:row-capacity) 32)
(= (ty_list:slot-count) 40)
(= (ty_list:pending-count) 48)
(= (ty_list:log-capacity) 56)
(= (ty_list:tail) 64)
(= (ty_list:key0) 72)
(= (ty_list:key1) 80)
(= (ty_list:hash) 88)
(= (ty_list:slot) 96)
(= (ty_list:entry) 104)
(= (ty_list:may-append) 112)
(= (ty_list:log-start) 128)
(= (ty_list:probe-cap) 16777216)
(= (ty_list:chunk-size) 2147483648)

(= (ty_list:get $offset $dst)
   (Seq (Base $dst work) (Load work $dst $dst $offset)))
(= (ty_list:put $offset $value $addr)
   (Seq (Base $addr work) (Store work $addr $offset $value)))
(= (ty_list:unsupported)
   (Seq (Imm t11 0) (Return UNSUPPORTED t11)))
(= (ty_list:refused)
   (Seq (Imm t11 0) (Return REFUSED t11)))

(= (ty_list:validate-layout)
   (Block ty_list_validate_layout
     (With (As first t8) (As items t9) (As cap t10) (As fits t11)
       (Arg0 first) (Arg1 items) (Len cap operands) (Shr cap cap 3)
       (Cmp Ule fits first cap) (If fits Skip (ty_list:unsupported))
       (Sub cap cap first) (Cmp Ule fits items cap)
       (If fits Skip (ty_list:unsupported))
       (ty_list:put (ty_list:first) first t11)
       (ty_list:put (ty_list:length) items t11)
       (Base first y-count) (Load y-count items first 0)
       (Len cap y-map) (Shr cap cap 3)
       (Cmp Ule fits items cap) (If fits Skip (ty_list:unsupported))
       (Len cap y-marks) (Shr cap cap 3)
       (Cmp Ule fits items cap) (If fits Skip (ty_list:unsupported))
       (ty_list:put (ty_list:y-count) items t11))))

; t8 is the zero-based position from the start of the list. It becomes its Y id.
(= (ty_list:read-operand)
   (Seq (ty_list:get (ty_list:first) t9)
        (Add t8 t8 t9) (Base t9 operands)
        (Addr operands t9 t9 t8 3 0) (Load operands t8 t9 0)))

(= (ty_list:validate-operand)
   (Block ty_list_validate_operand
     (Shl t8 chunk 31) (Add t8 t8 item)
     (ty_list:read-operand)
     (ty_list:get (ty_list:y-count) t9) (Cmp Ult t10 t8 t9)
     (If t10 Skip (ty_list:refused))
     (Base t9 y-marks) (Addr y-marks t9 t9 t8 3 0)
     (Load y-marks t9 t9 0) (CmpI Eq t10 t9 0)
     (If t10 Skip (ty_list:refused))))

; Two levels cover the full input interval admitted by the operand region.
(= (ty_list:walk-chunk $body)
   (Seq (Shl t8 chunk 31) (ty_list:get (ty_list:length) items)
        (Sub items items t8)
        (Imm t8 (ty_list:chunk-size)) (Cmp Ult t9 t8 items)
        (If t9 (Mov items t8))
        (Loop item items 2147483648 $body)))
(= (ty_list:walk-operands $body)
   (Seq (ty_list:get (ty_list:length) t8)
        (Shr chunks t8 31) (Imm t9 1) (Add chunks chunks t9)
        (Loop chunk chunks 2147483648 (ty_list:walk-chunk $body))))

(= (ty_list:prepare-table)
   (Block ty_list_prepare_table
     (Base t8 count) (Load count t9 t8 0)
     (Len t8 rows) (Shr t8 t8 4) (Cmp Ule t10 t9 t8)
     (If t10 Skip (ty_list:unsupported))
     (ty_list:put (ty_list:old-count) t9 t11)
     (ty_list:put (ty_list:row-capacity) t8 t11)
     (Len t8 slots) (Shr t8 t8 3)
     (CmpI Ule t10 t8 (ty_list:probe-cap))
     (If t10 Skip (ty_list:unsupported))
     (ty_list:put (ty_list:slot-count) t8 t11)
     (Len t8 work) (Imm t9 (ty_list:log-start))
     (Sub t8 t8 t9) (Shr t8 t8 5)
     (ty_list:put (ty_list:log-capacity) t8 t11)
     (Imm t8 0)
     (ty_list:put (ty_list:pending-count) t8 t11)
     (ty_list:put (ty_list:may-append) t8 t11)
     (ty_list:put (ty_list:key1) t8 t11)
     (Imm t8 2) (ty_list:put (ty_list:key0) t8 t11)))

; Only original empty slots can have a work-log replacement. The replacement
; word is the planned row id plus one, as in intern16.
(= (ty_list:lookup-log)
   (Block ty_list_lookup_log
     (ty_list:get (ty_list:pending-count) t9)
     (Loop t8 t9 16777216
       (Seq (Shl t10 t8 2) (Base t11 work)
            (Addr work t10 t11 t10 3 (ty_list:log-start))
            (Load work t10 t10 16)
            (ty_list:get (ty_list:slot) t11)
            (Cmp Eq t11 t10 t11)
            (If t11
                (Seq (ty_list:get (ty_list:old-count) t10)
                     (Add t10 t10 t8) (Imm t11 1) (Add t10 t10 t11)
                     (ty_list:put (ty_list:entry) t10 t11)))))))

; t8 is the candidate row id and t9 is its row address, either in rows or work.
(= (ty_list:compare-key $region)
   (Seq (Load $region t10 t9 0) (ty_list:get (ty_list:key0) t11)
        (Cmp Eq t11 t10 t11)
        (If t11
            (Seq (Load $region t10 t9 8) (ty_list:get (ty_list:key1) t11)
                 (Cmp Eq t11 t10 t11)
                 (If t11
                     (Seq (ty_list:put (ty_list:tail) t8 t10)
                          (Imm TyBool seeking 0)))))))

(= (ty_list:check-occupied)
   (Block ty_list_check_occupied
     (Imm t9 1) (Sub t8 t8 t9)
     (ty_list:get (ty_list:old-count) t9)
     (ty_list:get (ty_list:pending-count) t10) (Add t10 t9 t10)
     (Cmp Ult t11 t8 t10)
     (If t11
         (Seq (Cmp Ult t11 t8 t9)
              (If t11
                  (Seq (Shl t10 t8 1) (Base t9 rows) (Addr rows t9 t9 t10 3 0)
                       (ty_list:compare-key rows))
                  (Seq (Sub t10 t8 t9) (Shl t10 t10 2) (Base t9 work)
                       (Addr work t9 t9 t10 3 (ty_list:log-start))
                       (ty_list:compare-key work)))))))

(= (ty_list:plan-insertion)
   (Block ty_list_plan_insertion
     (ty_list:get (ty_list:may-append) t11) (CmpI Eq t11 t11 0)
     (If t11 (ty_list:unsupported))
     (ty_list:get (ty_list:pending-count) t8)
     (ty_list:get (ty_list:log-capacity) t9) (Cmp Ult t10 t8 t9)
     (If t10 Skip (ty_list:unsupported))
     (ty_list:get (ty_list:old-count) t9) (Add t9 t9 t8)
     (ty_list:get (ty_list:row-capacity) t10) (Cmp Ult t11 t9 t10)
     (If t11 Skip (ty_list:unsupported))
     (Shl t10 t8 2) (Base t11 work)
     (Addr work t10 t11 t10 3 (ty_list:log-start))
     (ty_list:get (ty_list:key0) t11) (Store work t10 0 t11)
     (ty_list:get (ty_list:key1) t11) (Store work t10 8 t11)
     (ty_list:get (ty_list:slot) t11) (Store work t10 16 t11)
     (ty_list:put (ty_list:tail) t9 t11)
     (Imm t11 1) (Add t8 t8 t11)
     (ty_list:put (ty_list:pending-count) t8 t10)
     (Imm TyBool seeking 0)))

(= (ty_list:probe)
   (Block ty_list_probe
     (ty_list:get (ty_list:hash) t8) (Add t8 t8 probe)
     (Imm t9 1) (Sub t9 probes t9) (And t8 t8 t9)
     (ty_list:put (ty_list:slot) t8 t9)
     (Base t9 slots) (Addr slots t9 t9 t8 3 0) (Load slots t8 t9 0)
     (ty_list:put (ty_list:entry) t8 t9) (CmpI Eq t10 t8 0)
     (If t10 (ty_list:lookup-log))
     (ty_list:get (ty_list:entry) t8)
     (CmpI Eq t10 t8 0)
     (If t10 (ty_list:plan-insertion) (ty_list:check-occupied))))

(= (ty_list:search)
   (Block ty_list_search
     (Seq (ty_list:get (ty_list:key0) t8) (ty_list:get (ty_list:key1) t9)
          (Xor t8 t8 t9) (Imm t9 11400714819323198485) (Mul t8 t8 t9)
          (Shr t9 t8 29) (Xor t8 t8 t9) (ty_list:put (ty_list:hash) t8 t9)
          (ty_list:get (ty_list:slot-count) probes)
          (Imm TyBool seeking 1)
          (EarlyLoop probe probes seeking 16777216 (ty_list:probe))
          (If seeking (ty_list:unsupported)))))

(= (ty_list:plan-operand)
   (Block ty_list_plan_operand
     (Shl t8 chunk 31) (Add t8 t8 item)
     (ty_list:get (ty_list:length) t9)
     (Imm t10 1) (Sub t9 t9 t10) (Sub t8 t9 t8)
     (ty_list:read-operand)
     (Base t9 y-map) (Addr y-map t9 t9 t8 3 0) (Load y-map t8 t9 0)
     (ty_list:get (ty_list:old-count) t9) (Cmp Ult t10 t8 t9)
     (If t10 Skip (ty_list:unsupported))
     (Shl t8 t8 3) (Imm t9 3) (Add t8 t8 t9)
     (ty_list:put (ty_list:key0) t8 t9)
     (ty_list:get (ty_list:tail) t8) (ty_list:put (ty_list:key1) t8 t9)
     (ty_list:search)))

(= (ty_list:commit-row)
   (Block ty_list_commit_row
     (Shl t9 probe 2) (Base t8 work)
     (Addr work t8 t8 t9 3 (ty_list:log-start))
     (ty_list:get (ty_list:old-count) t9) (Add t9 t9 probe)
     (Shl t11 t9 1) (Base t10 rows) (Addr rows t10 t10 t11 3 0)
     (Load work t11 t8 0) (Store rows t10 0 t11)
     (Load work t11 t8 8) (Store rows t10 8 t11)
     (Load work t11 t8 16) (Base t10 slots) (Addr slots t10 t10 t11 3 0)
     (Imm t11 1) (Add t9 t9 t11) (Store slots t10 0 t9)))

(= (ty_list:publish)
   (Block ty_list_publish
     (ty_list:get (ty_list:pending-count) probes)
     (Loop probe probes 16777216 (ty_list:commit-row))
     (CmpI Ne t10 probes 0)
     (If t10 (Seq (ty_list:get (ty_list:old-count) t9) (Add t9 t9 probes)
                  (Base t8 count) (Store count t8 0 t9)))
     (ty_list:get (ty_list:tail) t8) (Return FIRED t8)))

(= (ty_list:program)
   (p1:program ty_list
     (Regions (Region rows RW 16 8) (Region slots RW 8 8) (Region count RW 8 8)
              (Region y-map RO 0 8) (Region y-count RO 8 8) (Region y-marks RO 0 8)
              (Region operands RO 0 8) (Region work RW 256 8))
     (Registers (As chunk v1) (As chunks v2) (As item v3) (As items v4)
                (As probe v5) (As probes v6) (As seeking v7)
                (As t8 v8) (As t9 v9) (As t10 v10) (As t11 v11))
     (Init)
     (Seq (ty_list:validate-layout)
          (Block ty_list_validate_all (ty_list:walk-operands (ty_list:validate-operand)))
          (ty_list:prepare-table)
          (ty_list:search)
          (Imm t8 1) (ty_list:put (ty_list:may-append) t8 t9)
          (Block ty_list_plan_all (ty_list:walk-operands (ty_list:plan-operand)))
          (ty_list:publish))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write ty_list:program $text $notes))
