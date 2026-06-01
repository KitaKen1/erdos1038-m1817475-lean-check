import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block490

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block490

open Set

def block490W1 : Rat := ((9758723592056191 : Rat) / 20000000000000000)
def block490W2 : Rat := (0 : Rat)
def block490W3 : Rat := ((1978964639277941 : Rat) / 5000000000000000)
def block490W4 : Rat := ((15798965040075823 : Rat) / 500000000000000000)
def block490S1 : Rat := ((18174751 : Rat) / 10000000)
def block490S2 : Rat := ((511587 : Rat) / 200000)
def block490S3 : Rat := ((130554494732142857283 : Rat) / 50000000000000000000)
def block490S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block490V (y : ℝ) : ℝ :=
  ratPotential block490W1 block490W2 block490W3 block490W4 block490S1 block490S2 block490S3 block490S4 y

def block490LeftParamsCertificate : Bool :=
  allBoxesSameParams block490LeftBoxes block490W1 block490W2 block490W3 block490W4 block490S1 block490S2 block490S3 block490S4

theorem block490LeftParamsCertificate_eq_true :
    block490LeftParamsCertificate = true := by
  native_decide

theorem block490_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block490LeftL : ℝ) (block490LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block490S1 : ℝ))
    (hy2ne : y ≠ (block490S2 : ℝ))
    (hy3ne : y ≠ (block490S3 : ℝ))
    (hy4ne : y ≠ (block490S4 : ℝ)) :
    0 < block490V y := by
  have hcert := block490LeftCertificate_eq_true
  unfold block490LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block490LeftBoxes) (lo := block490LeftL) (hi := block490LeftR)
    (w1 := block490W1) (w2 := block490W2) (w3 := block490W3) (w4 := block490W4)
    (s1 := block490S1) (s2 := block490S2) (s3 := block490S3) (s4 := block490S4)
    hboxes hcover block490LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block490RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block490RightChunk000 block490W1 block490W2 block490W3 block490W4 block490S1 block490S2 block490S3 block490S4

theorem block490RightChunk000ParamsCertificate_eq_true :
    block490RightChunk000ParamsCertificate = true := by
  native_decide

theorem block490_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block490RightChunk000L : ℝ) (block490RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block490S1 : ℝ))
    (hy2ne : y ≠ (block490S2 : ℝ))
    (hy3ne : y ≠ (block490S3 : ℝ))
    (hy4ne : y ≠ (block490S4 : ℝ)) :
    0 < block490V y := by
  have hcert := block490RightChunk000Certificate_eq_true
  unfold block490RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block490RightChunk000) (lo := block490RightChunk000L) (hi := block490RightChunk000R)
    (w1 := block490W1) (w2 := block490W2) (w3 := block490W3) (w4 := block490W4)
    (s1 := block490S1) (s2 := block490S2) (s3 := block490S3) (s4 := block490S4)
    hboxes hcover block490RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block490_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block490RightL : ℝ) (block490RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block490S1 : ℝ))
    (hy2ne : y ≠ (block490S2 : ℝ))
    (hy3ne : y ≠ (block490S3 : ℝ))
    (hy4ne : y ≠ (block490S4 : ℝ)) :
    0 < block490V y := by
  have hL : (block490RightChunk000L : ℝ) = (block490RightL : ℝ) := by
    norm_num [block490RightChunk000L, block490RightL]
  have hR : (block490RightChunk000R : ℝ) = (block490RightR : ℝ) := by
    norm_num [block490RightChunk000R, block490RightR]
  have hyc : y ∈ Icc (block490RightChunk000L : ℝ) (block490RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block490_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block490_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block490LeftL : ℝ) (block490LeftR : ℝ) →
    y ≠ 0 → y ≠ (block490S1 : ℝ) → y ≠ (block490S2 : ℝ) →
    y ≠ (block490S3 : ℝ) → y ≠ (block490S4 : ℝ) → 0 < block490V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block490RightL : ℝ) (block490RightR : ℝ) →
    y ≠ 0 → y ≠ (block490S1 : ℝ) → y ≠ (block490S2 : ℝ) →
    y ≠ (block490S3 : ℝ) → y ≠ (block490S4 : ℝ) → 0 < block490V y)

theorem block490_reallog_certificate_proof :
    block490_reallog_certificate := by
  exact ⟨block490_left_V_pos, block490_right_V_pos⟩

end Block490
end M1817475
end Erdos1038Lean
