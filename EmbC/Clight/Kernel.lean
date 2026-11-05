import EmbC.Clight.Representation

/-! Abstract kernel wrappers at the EmbC-to-Clight semantic boundary.
Their signatures use the logical arguments of the kernel contracts; their correspondence
with the Linux ABI is a separate obligation. -/

namespace EmbC.Clight

private def typeName : Ty → String
  | .u32 => "u32"
  | .u64 => "u64"
  | .ptr t => "ptr_" ++ typeName t
  | .struct s => "struct_" ++ s
  | .bpfptr => "bpfptr"

def kernelName : Ext → String
  | .kvcalloc t => "__embc_kvcalloc_" ++ typeName t
  | .kzalloc s => "__embc_kzalloc_" ++ s
  | .kvrealloc t => "__embc_kvrealloc_" ++ typeName t
  | .kvfree => "__embc_kvfree"
  | .copyFromBpfptr => "__embc_copy_from_bpfptr"
  | .signalPending => "__embc_signal_pending"
  | .condResched => "__embc_cond_resched"

def kernelSignature : Ext → CC.Signature
  | .kvcalloc _ => CC.mksignature [.Xlong] .Xptr CC.cc_default
  | .kzalloc _ => CC.mksignature [] .Xptr CC.cc_default
  | .kvrealloc _ => CC.mksignature [.Xptr, .Xlong] .Xptr CC.cc_default
  | .kvfree => CC.mksignature [.Xptr] .Xvoid CC.cc_default
  | .copyFromBpfptr => CC.mksignature [.Xptr, .Xptr, .Xlong] .Xint CC.cc_default
  | .signalPending => CC.mksignature [] .Xint CC.cc_default
  | .condResched => CC.mksignature [] .Xvoid CC.cc_default

def kernelExternal (ext : Ext) : CC.ExtFun :=
  .EF_external (kernelName ext) (kernelSignature ext)

def argsRel (P : Prog) (m : Mem) (j : MemoryInjection) :
    List Val → List CC.Val → Prop
  | [], [] => True
  | v :: vs, w :: ws => valRel P m j v w ∧ argsRel P m j vs ws
  | _, _ => False

end EmbC.Clight
