/* Generated from NativeInterface.module. */
.equ TISA_ABI_CoreControls_opcode, 18
.equ TISA_ABI_CoreControls_reader_state, 21
.equ TISA_ABI_WordBytes, 8
.equ TISA_ABI_MaxRegions, 9
.equ TISA_ABI_FrameWords, 24
.equ TISA_ABI_FrameBytes, 192
.equ TISA_ABI_CFrameAlignment, 64
.equ TISA_ABI_LeafStackSaveBytes, 40
.equ TISA_ABI_DriveWords, 8
.equ TISA_ABI_StepWords, 18
.equ TISA_ABI_StepBytes, 144
.equ TISA_ABI_DriverCodeBytes, 522
.equ TISA_ABI_DriverFrameDistance, 248
.equ TISA_ABI_DriverWorkBytes, 304
.equ TISA_ABI_CallArgumentCount, 7
.equ TISA_ABI_CallRequestWords, 8
.equ TISA_ABI_CallRequestBytes, 64
.equ TISA_ABI_RuntimeFrame_s0_ptr, 0
.equ TISA_ABI_RuntimeFrame_s0_len, 1
.equ TISA_ABI_RuntimeFrame_s1_ptr, 2
.equ TISA_ABI_RuntimeFrame_s1_len, 3
.equ TISA_ABI_RuntimeFrame_s2_ptr, 4
.equ TISA_ABI_RuntimeFrame_s2_len, 5
.equ TISA_ABI_RuntimeFrame_s3_ptr, 6
.equ TISA_ABI_RuntimeFrame_s3_len, 7
.equ TISA_ABI_RuntimeFrame_s4_ptr, 8
.equ TISA_ABI_RuntimeFrame_s4_len, 9
.equ TISA_ABI_RuntimeFrame_s5_ptr, 10
.equ TISA_ABI_RuntimeFrame_s5_len, 11
.equ TISA_ABI_RuntimeFrame_s6_ptr, 12
.equ TISA_ABI_RuntimeFrame_s6_len, 13
.equ TISA_ABI_RuntimeFrame_s7_ptr, 14
.equ TISA_ABI_RuntimeFrame_s7_len, 15
.equ TISA_ABI_RuntimeFrame_s8_ptr, 16
.equ TISA_ABI_RuntimeFrame_s8_len, 17
.equ TISA_ABI_RuntimeFrame_status, 18
.equ TISA_ABI_RuntimeFrame_ret_val, 19
.equ TISA_ABI_RuntimeFrame_fuel_budget, 20
.equ TISA_ABI_RuntimeFrame_fuel_used, 21
.equ TISA_ABI_RuntimeFrame_arg0, 22
.equ TISA_ABI_RuntimeFrame_arg1, 23
.equ TISA_ABI_DriveDescriptor_plan, 0
.equ TISA_ABI_DriveDescriptor_plan_end, 1
.equ TISA_ABI_DriveDescriptor_ctl, 2
.equ TISA_ABI_DriveDescriptor_bind, 3
.equ TISA_ABI_DriveDescriptor_leaves, 4
.equ TISA_ABI_DriveDescriptor_budget, 5
.equ TISA_ABI_DriveDescriptor_used, 6
.equ TISA_ABI_DriveDescriptor_at, 7
.equ TISA_ABI_DriveStep_leaf, 0
.equ TISA_ABI_DriveStep_region_0, 1
.equ TISA_ABI_DriveStep_region_1, 2
.equ TISA_ABI_DriveStep_region_2, 3
.equ TISA_ABI_DriveStep_region_3, 4
.equ TISA_ABI_DriveStep_region_4, 5
.equ TISA_ABI_DriveStep_region_5, 6
.equ TISA_ABI_DriveStep_region_6, 7
.equ TISA_ABI_DriveStep_region_7, 8
.equ TISA_ABI_DriveStep_region_8, 9
.equ TISA_ABI_DriveStep_arg0, 10
.equ TISA_ABI_DriveStep_arg1, 11
.equ TISA_ABI_DriveStep_hot_1, 12
.equ TISA_ABI_DriveStep_hot_2, 13
.equ TISA_ABI_DriveStep_hot_3, 14
.equ TISA_ABI_DriveStep_hot_4, 15
.equ TISA_ABI_DriveStep_hot_5, 16
.equ TISA_ABI_DriveStep_dst, 17
.equ TISA_ABI_CallRequest_arg0, 0
.equ TISA_ABI_CallRequest_arg1, 1
.equ TISA_ABI_CallRequest_arg2, 2
.equ TISA_ABI_CallRequest_arg3, 3
.equ TISA_ABI_CallRequest_arg4, 4
.equ TISA_ABI_CallRequest_arg5, 5
.equ TISA_ABI_CallRequest_arg6, 6
.equ TISA_ABI_CallRequest_target, 7
.equ TISA_ABI_CoreControls_policy, 7
.equ TISA_ABI_CoreControls_count, 17
.equ TISA_ABI_CoreControls_end, 19
.equ TISA_ABI_CoreControls_header, 20
.equ TISA_ABI_CoreControls_fnv, 22
.equ TISA_ABI_ProcedureControls_result, 7
.equ TISA_ABI_ProcedureControls_arg0, 8
.equ TISA_ABI_ProcedureControls_arg1, 9
.equ TISA_ABI_ProcedureControls_arg2, 10
.equ TISA_ABI_ProcedureControls_arg3, 11
.equ TISA_ABI_ProcedureControls_arg4, 12
.equ TISA_ABI_ProcedureControls_arg5, 13
.equ TISA_ABI_ProcedureControls_arg6, 14
.equ TISA_ABI_CoreControls_opcode_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CoreControls_opcode
.equ TISA_ABI_CoreControls_reader_state_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CoreControls_reader_state
.equ TISA_ABI_RuntimeFrame_s0_ptr_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s0_ptr
.equ TISA_ABI_RuntimeFrame_s0_len_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s0_len
.equ TISA_ABI_RuntimeFrame_s1_ptr_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s1_ptr
.equ TISA_ABI_RuntimeFrame_s1_len_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s1_len
.equ TISA_ABI_RuntimeFrame_s2_ptr_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s2_ptr
.equ TISA_ABI_RuntimeFrame_s2_len_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s2_len
.equ TISA_ABI_RuntimeFrame_s3_ptr_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s3_ptr
.equ TISA_ABI_RuntimeFrame_s3_len_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s3_len
.equ TISA_ABI_RuntimeFrame_s4_ptr_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s4_ptr
.equ TISA_ABI_RuntimeFrame_s4_len_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s4_len
.equ TISA_ABI_RuntimeFrame_s5_ptr_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s5_ptr
.equ TISA_ABI_RuntimeFrame_s5_len_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s5_len
.equ TISA_ABI_RuntimeFrame_s6_ptr_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s6_ptr
.equ TISA_ABI_RuntimeFrame_s6_len_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s6_len
.equ TISA_ABI_RuntimeFrame_s7_ptr_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s7_ptr
.equ TISA_ABI_RuntimeFrame_s7_len_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s7_len
.equ TISA_ABI_RuntimeFrame_s8_ptr_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s8_ptr
.equ TISA_ABI_RuntimeFrame_s8_len_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_s8_len
.equ TISA_ABI_RuntimeFrame_status_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_status
.equ TISA_ABI_RuntimeFrame_ret_val_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_ret_val
.equ TISA_ABI_RuntimeFrame_fuel_budget_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_fuel_budget
.equ TISA_ABI_RuntimeFrame_fuel_used_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_fuel_used
.equ TISA_ABI_RuntimeFrame_arg0_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_arg0
.equ TISA_ABI_RuntimeFrame_arg1_OFFSET, TISA_ABI_WordBytes * TISA_ABI_RuntimeFrame_arg1
.equ TISA_ABI_DriveDescriptor_plan_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveDescriptor_plan
.equ TISA_ABI_DriveDescriptor_plan_end_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveDescriptor_plan_end
.equ TISA_ABI_DriveDescriptor_ctl_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveDescriptor_ctl
.equ TISA_ABI_DriveDescriptor_bind_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveDescriptor_bind
.equ TISA_ABI_DriveDescriptor_leaves_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveDescriptor_leaves
.equ TISA_ABI_DriveDescriptor_budget_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveDescriptor_budget
.equ TISA_ABI_DriveDescriptor_used_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveDescriptor_used
.equ TISA_ABI_DriveDescriptor_at_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveDescriptor_at
.equ TISA_ABI_DriveStep_leaf_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_leaf
.equ TISA_ABI_DriveStep_region_0_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_region_0
.equ TISA_ABI_DriveStep_region_1_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_region_1
.equ TISA_ABI_DriveStep_region_2_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_region_2
.equ TISA_ABI_DriveStep_region_3_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_region_3
.equ TISA_ABI_DriveStep_region_4_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_region_4
.equ TISA_ABI_DriveStep_region_5_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_region_5
.equ TISA_ABI_DriveStep_region_6_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_region_6
.equ TISA_ABI_DriveStep_region_7_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_region_7
.equ TISA_ABI_DriveStep_region_8_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_region_8
.equ TISA_ABI_DriveStep_arg0_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_arg0
.equ TISA_ABI_DriveStep_arg1_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_arg1
.equ TISA_ABI_DriveStep_hot_1_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_hot_1
.equ TISA_ABI_DriveStep_hot_2_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_hot_2
.equ TISA_ABI_DriveStep_hot_3_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_hot_3
.equ TISA_ABI_DriveStep_hot_4_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_hot_4
.equ TISA_ABI_DriveStep_hot_5_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_hot_5
.equ TISA_ABI_DriveStep_dst_OFFSET, TISA_ABI_WordBytes * TISA_ABI_DriveStep_dst
.equ TISA_ABI_CallRequest_arg0_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CallRequest_arg0
.equ TISA_ABI_CallRequest_arg1_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CallRequest_arg1
.equ TISA_ABI_CallRequest_arg2_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CallRequest_arg2
.equ TISA_ABI_CallRequest_arg3_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CallRequest_arg3
.equ TISA_ABI_CallRequest_arg4_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CallRequest_arg4
.equ TISA_ABI_CallRequest_arg5_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CallRequest_arg5
.equ TISA_ABI_CallRequest_arg6_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CallRequest_arg6
.equ TISA_ABI_CallRequest_target_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CallRequest_target
.equ TISA_ABI_CoreControls_policy_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CoreControls_policy
.equ TISA_ABI_CoreControls_count_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CoreControls_count
.equ TISA_ABI_CoreControls_end_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CoreControls_end
.equ TISA_ABI_CoreControls_header_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CoreControls_header
.equ TISA_ABI_CoreControls_fnv_OFFSET, TISA_ABI_WordBytes * TISA_ABI_CoreControls_fnv
.equ TISA_ABI_ProcedureControls_result_OFFSET, TISA_ABI_WordBytes * TISA_ABI_ProcedureControls_result
.equ TISA_ABI_ProcedureControls_arg0_OFFSET, TISA_ABI_WordBytes * TISA_ABI_ProcedureControls_arg0
.equ TISA_ABI_ProcedureControls_arg1_OFFSET, TISA_ABI_WordBytes * TISA_ABI_ProcedureControls_arg1
.equ TISA_ABI_ProcedureControls_arg2_OFFSET, TISA_ABI_WordBytes * TISA_ABI_ProcedureControls_arg2
.equ TISA_ABI_ProcedureControls_arg3_OFFSET, TISA_ABI_WordBytes * TISA_ABI_ProcedureControls_arg3
.equ TISA_ABI_ProcedureControls_arg4_OFFSET, TISA_ABI_WordBytes * TISA_ABI_ProcedureControls_arg4
.equ TISA_ABI_ProcedureControls_arg5_OFFSET, TISA_ABI_WordBytes * TISA_ABI_ProcedureControls_arg5
.equ TISA_ABI_ProcedureControls_arg6_OFFSET, TISA_ABI_WordBytes * TISA_ABI_ProcedureControls_arg6
