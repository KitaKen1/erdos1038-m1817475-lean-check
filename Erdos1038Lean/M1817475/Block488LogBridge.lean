import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block488

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block488

open Set

def block488W1 : Rat := ((12325663987091509 : Rat) / 25000000000000000)
def block488W2 : Rat := (0 : Rat)
def block488W3 : Rat := ((1961758530881563 : Rat) / 5000000000000000)
def block488W4 : Rat := ((336327790773773 : Rat) / 10000000000000000)
def block488S1 : Rat := ((18174751 : Rat) / 10000000)
def block488S2 : Rat := ((511587 : Rat) / 200000)
def block488S3 : Rat := ((130593592946428571567 : Rat) / 50000000000000000000)
def block488S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block488V (y : ℝ) : ℝ :=
  ratPotential block488W1 block488W2 block488W3 block488W4 block488S1 block488S2 block488S3 block488S4 y

def block488LeftParamsCertificate : Bool :=
  allBoxesSameParams block488LeftBoxes block488W1 block488W2 block488W3 block488W4 block488S1 block488S2 block488S3 block488S4

theorem block488LeftParamsCertificate_eq_true :
    block488LeftParamsCertificate = true := by
  native_decide

theorem block488_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block488LeftL : ℝ) (block488LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block488S1 : ℝ))
    (hy2ne : y ≠ (block488S2 : ℝ))
    (hy3ne : y ≠ (block488S3 : ℝ))
    (hy4ne : y ≠ (block488S4 : ℝ)) :
    0 < block488V y := by
  have hcert := block488LeftCertificate_eq_true
  unfold block488LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block488LeftBoxes) (lo := block488LeftL) (hi := block488LeftR)
    (w1 := block488W1) (w2 := block488W2) (w3 := block488W3) (w4 := block488W4)
    (s1 := block488S1) (s2 := block488S2) (s3 := block488S3) (s4 := block488S4)
    hboxes hcover block488LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block488RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block488RightChunk000 block488W1 block488W2 block488W3 block488W4 block488S1 block488S2 block488S3 block488S4

theorem block488RightChunk000ParamsCertificate_eq_true :
    block488RightChunk000ParamsCertificate = true := by
  native_decide

theorem block488_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block488RightChunk000L : ℝ) (block488RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block488S1 : ℝ))
    (hy2ne : y ≠ (block488S2 : ℝ))
    (hy3ne : y ≠ (block488S3 : ℝ))
    (hy4ne : y ≠ (block488S4 : ℝ)) :
    0 < block488V y := by
  have hcert := block488RightChunk000Certificate_eq_true
  unfold block488RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block488RightChunk000) (lo := block488RightChunk000L) (hi := block488RightChunk000R)
    (w1 := block488W1) (w2 := block488W2) (w3 := block488W3) (w4 := block488W4)
    (s1 := block488S1) (s2 := block488S2) (s3 := block488S3) (s4 := block488S4)
    hboxes hcover block488RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block488_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block488RightL : ℝ) (block488RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block488S1 : ℝ))
    (hy2ne : y ≠ (block488S2 : ℝ))
    (hy3ne : y ≠ (block488S3 : ℝ))
    (hy4ne : y ≠ (block488S4 : ℝ)) :
    0 < block488V y := by
  have hL : (block488RightChunk000L : ℝ) = (block488RightL : ℝ) := by
    norm_num [block488RightChunk000L, block488RightL]
  have hR : (block488RightChunk000R : ℝ) = (block488RightR : ℝ) := by
    norm_num [block488RightChunk000R, block488RightR]
  have hyc : y ∈ Icc (block488RightChunk000L : ℝ) (block488RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block488_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block488_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block488LeftL : ℝ) (block488LeftR : ℝ) →
    y ≠ 0 → y ≠ (block488S1 : ℝ) → y ≠ (block488S2 : ℝ) →
    y ≠ (block488S3 : ℝ) → y ≠ (block488S4 : ℝ) → 0 < block488V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block488RightL : ℝ) (block488RightR : ℝ) →
    y ≠ 0 → y ≠ (block488S1 : ℝ) → y ≠ (block488S2 : ℝ) →
    y ≠ (block488S3 : ℝ) → y ≠ (block488S4 : ℝ) → 0 < block488V y)

theorem block488_reallog_certificate_proof :
    block488_reallog_certificate := by
  exact ⟨block488_left_V_pos, block488_right_V_pos⟩

end Block488
end M1817475
end Erdos1038Lean
