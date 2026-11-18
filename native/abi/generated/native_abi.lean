import Mettapedia.Machines.TIsa.Layout
-- Generated from NativeInterface.module.
namespace TIsa.NativeABI
def CoreControls_opcode : Nat := 18
def CoreControls_reader_state : Nat := 21
def WordBytes : Nat := 8
def MaxRegions : Nat := 9
def FrameWords : Nat := 24
def FrameBytes : Nat := 192
def CFrameAlignment : Nat := 64
def LeafStackSaveBytes : Nat := 40
def DriveWords : Nat := 8
def StepWords : Nat := 18
def StepBytes : Nat := 144
def DriverCodeBytes : Nat := 522
def DriverFrameDistance : Nat := 248
def DriverWorkBytes : Nat := 304
def CallArgumentCount : Nat := 7
def CallRequestWords : Nat := 8
def CallRequestBytes : Nat := 64
def RuntimeFrame_s0_ptr : Nat := 0
def RuntimeFrame_s0_len : Nat := 1
def RuntimeFrame_s1_ptr : Nat := 2
def RuntimeFrame_s1_len : Nat := 3
def RuntimeFrame_s2_ptr : Nat := 4
def RuntimeFrame_s2_len : Nat := 5
def RuntimeFrame_s3_ptr : Nat := 6
def RuntimeFrame_s3_len : Nat := 7
def RuntimeFrame_s4_ptr : Nat := 8
def RuntimeFrame_s4_len : Nat := 9
def RuntimeFrame_s5_ptr : Nat := 10
def RuntimeFrame_s5_len : Nat := 11
def RuntimeFrame_s6_ptr : Nat := 12
def RuntimeFrame_s6_len : Nat := 13
def RuntimeFrame_s7_ptr : Nat := 14
def RuntimeFrame_s7_len : Nat := 15
def RuntimeFrame_s8_ptr : Nat := 16
def RuntimeFrame_s8_len : Nat := 17
def RuntimeFrame_status : Nat := 18
def RuntimeFrame_ret_val : Nat := 19
def RuntimeFrame_fuel_budget : Nat := 20
def RuntimeFrame_fuel_used : Nat := 21
def RuntimeFrame_arg0 : Nat := 22
def RuntimeFrame_arg1 : Nat := 23
def DriveDescriptor_plan : Nat := 0
def DriveDescriptor_plan_end : Nat := 1
def DriveDescriptor_ctl : Nat := 2
def DriveDescriptor_bind : Nat := 3
def DriveDescriptor_leaves : Nat := 4
def DriveDescriptor_budget : Nat := 5
def DriveDescriptor_used : Nat := 6
def DriveDescriptor_at : Nat := 7
def DriveStep_leaf : Nat := 0
def DriveStep_region_0 : Nat := 1
def DriveStep_region_1 : Nat := 2
def DriveStep_region_2 : Nat := 3
def DriveStep_region_3 : Nat := 4
def DriveStep_region_4 : Nat := 5
def DriveStep_region_5 : Nat := 6
def DriveStep_region_6 : Nat := 7
def DriveStep_region_7 : Nat := 8
def DriveStep_region_8 : Nat := 9
def DriveStep_arg0 : Nat := 10
def DriveStep_arg1 : Nat := 11
def DriveStep_hot_1 : Nat := 12
def DriveStep_hot_2 : Nat := 13
def DriveStep_hot_3 : Nat := 14
def DriveStep_hot_4 : Nat := 15
def DriveStep_hot_5 : Nat := 16
def DriveStep_dst : Nat := 17
def CallRequest_arg0 : Nat := 0
def CallRequest_arg1 : Nat := 1
def CallRequest_arg2 : Nat := 2
def CallRequest_arg3 : Nat := 3
def CallRequest_arg4 : Nat := 4
def CallRequest_arg5 : Nat := 5
def CallRequest_arg6 : Nat := 6
def CallRequest_target : Nat := 7
def CoreControls_policy : Nat := 7
def CoreControls_count : Nat := 17
def CoreControls_end : Nat := 19
def CoreControls_header : Nat := 20
def CoreControls_fnv : Nat := 22
def ProcedureControls_result : Nat := 7
def ProcedureControls_arg0 : Nat := 8
def ProcedureControls_arg1 : Nat := 9
def ProcedureControls_arg2 : Nat := 10
def ProcedureControls_arg3 : Nat := 11
def ProcedureControls_arg4 : Nat := 12
def ProcedureControls_arg5 : Nat := 13
def ProcedureControls_arg6 : Nat := 14
def RuntimeFrameLayout : Mettapedia.Machines.TIsa.Layout :=
  ⟨FrameBytes, CFrameAlignment, [
⟨"s0_ptr", WordBytes * RuntimeFrame_s0_ptr, WordBytes, .pointer (RuntimeFrame_s0_ptr / 2)⟩,
⟨"s0_len", WordBytes * RuntimeFrame_s0_len, WordBytes, .u64⟩,
⟨"s1_ptr", WordBytes * RuntimeFrame_s1_ptr, WordBytes, .pointer (RuntimeFrame_s1_ptr / 2)⟩,
⟨"s1_len", WordBytes * RuntimeFrame_s1_len, WordBytes, .u64⟩,
⟨"s2_ptr", WordBytes * RuntimeFrame_s2_ptr, WordBytes, .pointer (RuntimeFrame_s2_ptr / 2)⟩,
⟨"s2_len", WordBytes * RuntimeFrame_s2_len, WordBytes, .u64⟩,
⟨"s3_ptr", WordBytes * RuntimeFrame_s3_ptr, WordBytes, .pointer (RuntimeFrame_s3_ptr / 2)⟩,
⟨"s3_len", WordBytes * RuntimeFrame_s3_len, WordBytes, .u64⟩,
⟨"s4_ptr", WordBytes * RuntimeFrame_s4_ptr, WordBytes, .pointer (RuntimeFrame_s4_ptr / 2)⟩,
⟨"s4_len", WordBytes * RuntimeFrame_s4_len, WordBytes, .u64⟩,
⟨"s5_ptr", WordBytes * RuntimeFrame_s5_ptr, WordBytes, .pointer (RuntimeFrame_s5_ptr / 2)⟩,
⟨"s5_len", WordBytes * RuntimeFrame_s5_len, WordBytes, .u64⟩,
⟨"s6_ptr", WordBytes * RuntimeFrame_s6_ptr, WordBytes, .pointer (RuntimeFrame_s6_ptr / 2)⟩,
⟨"s6_len", WordBytes * RuntimeFrame_s6_len, WordBytes, .u64⟩,
⟨"s7_ptr", WordBytes * RuntimeFrame_s7_ptr, WordBytes, .pointer (RuntimeFrame_s7_ptr / 2)⟩,
⟨"s7_len", WordBytes * RuntimeFrame_s7_len, WordBytes, .u64⟩,
⟨"s8_ptr", WordBytes * RuntimeFrame_s8_ptr, WordBytes, .pointer (RuntimeFrame_s8_ptr / 2)⟩,
⟨"s8_len", WordBytes * RuntimeFrame_s8_len, WordBytes, .u64⟩,
⟨"status", WordBytes * RuntimeFrame_status, WordBytes, .u64⟩,
⟨"ret_val", WordBytes * RuntimeFrame_ret_val, WordBytes, .u64⟩,
⟨"fuel_budget", WordBytes * RuntimeFrame_fuel_budget, WordBytes, .u64⟩,
⟨"fuel_used", WordBytes * RuntimeFrame_fuel_used, WordBytes, .u64⟩,
⟨"arg0", WordBytes * RuntimeFrame_arg0, WordBytes, .u64⟩,
⟨"arg1", WordBytes * RuntimeFrame_arg1, WordBytes, .u64⟩,
]⟩
end TIsa.NativeABI
