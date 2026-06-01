import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block006

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block006

open Set

def block006W1 : Rat := ((11242826608099557 : Rat) / 1000000000000000)
def block006W2 : Rat := (0 : Rat)
def block006W3 : Rat := (0 : Rat)
def block006W4 : Rat := ((2501050100397023 : Rat) / 10000000000000000)
def block006S1 : Rat := ((18174751 : Rat) / 10000000)
def block006S2 : Rat := ((511587 : Rat) / 200000)
def block006S3 : Rat := ((107000619 : Rat) / 40000000)
def block006S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block006V (y : ℝ) : ℝ :=
  ratPotential block006W1 block006W2 block006W3 block006W4 block006S1 block006S2 block006S3 block006S4 y

def block006LeftParamsCertificate : Bool :=
  allBoxesSameParams block006LeftBoxes block006W1 block006W2 block006W3 block006W4 block006S1 block006S2 block006S3 block006S4

theorem block006LeftParamsCertificate_eq_true :
    block006LeftParamsCertificate = true := by
  native_decide

theorem block006_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block006LeftL : ℝ) (block006LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block006S1 : ℝ))
    (hy2ne : y ≠ (block006S2 : ℝ))
    (hy3ne : y ≠ (block006S3 : ℝ))
    (hy4ne : y ≠ (block006S4 : ℝ)) :
    0 < block006V y := by
  have hcert := block006LeftCertificate_eq_true
  unfold block006LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block006LeftBoxes) (lo := block006LeftL) (hi := block006LeftR)
    (w1 := block006W1) (w2 := block006W2) (w3 := block006W3) (w4 := block006W4)
    (s1 := block006S1) (s2 := block006S2) (s3 := block006S3) (s4 := block006S4)
    hboxes hcover block006LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block006RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block006RightChunk000 block006W1 block006W2 block006W3 block006W4 block006S1 block006S2 block006S3 block006S4

theorem block006RightChunk000ParamsCertificate_eq_true :
    block006RightChunk000ParamsCertificate = true := by
  native_decide

theorem block006_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block006RightChunk000L : ℝ) (block006RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block006S1 : ℝ))
    (hy2ne : y ≠ (block006S2 : ℝ))
    (hy3ne : y ≠ (block006S3 : ℝ))
    (hy4ne : y ≠ (block006S4 : ℝ)) :
    0 < block006V y := by
  have hcert := block006RightChunk000Certificate_eq_true
  unfold block006RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block006RightChunk000) (lo := block006RightChunk000L) (hi := block006RightChunk000R)
    (w1 := block006W1) (w2 := block006W2) (w3 := block006W3) (w4 := block006W4)
    (s1 := block006S1) (s2 := block006S2) (s3 := block006S3) (s4 := block006S4)
    hboxes hcover block006RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block006_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block006RightL : ℝ) (block006RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block006S1 : ℝ))
    (hy2ne : y ≠ (block006S2 : ℝ))
    (hy3ne : y ≠ (block006S3 : ℝ))
    (hy4ne : y ≠ (block006S4 : ℝ)) :
    0 < block006V y := by
  have hL : (block006RightChunk000L : ℝ) = (block006RightL : ℝ) := by
    norm_num [block006RightChunk000L, block006RightL]
  have hR : (block006RightChunk000R : ℝ) = (block006RightR : ℝ) := by
    norm_num [block006RightChunk000R, block006RightR]
  have hyc : y ∈ Icc (block006RightChunk000L : ℝ) (block006RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block006_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block006_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block006LeftL : ℝ) (block006LeftR : ℝ) →
    y ≠ 0 → y ≠ (block006S1 : ℝ) → y ≠ (block006S2 : ℝ) →
    y ≠ (block006S3 : ℝ) → y ≠ (block006S4 : ℝ) → 0 < block006V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block006RightL : ℝ) (block006RightR : ℝ) →
    y ≠ 0 → y ≠ (block006S1 : ℝ) → y ≠ (block006S2 : ℝ) →
    y ≠ (block006S3 : ℝ) → y ≠ (block006S4 : ℝ) → 0 < block006V y)

theorem block006_reallog_certificate_proof :
    block006_reallog_certificate := by
  exact ⟨block006_left_V_pos, block006_right_V_pos⟩

end Block006
end M1817475
end Erdos1038Lean
