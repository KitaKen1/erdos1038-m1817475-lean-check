import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block516

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block516

open Set

def block516W1 : Rat := ((21131229375387167 : Rat) / 50000000000000000)
def block516W2 : Rat := (0 : Rat)
def block516W3 : Rat := ((4468926242861029 : Rat) / 10000000000000000)
def block516W4 : Rat := (0 : Rat)
def block516S1 : Rat := ((18174751 : Rat) / 10000000)
def block516S2 : Rat := ((511587 : Rat) / 200000)
def block516S3 : Rat := ((130046217946428571591 : Rat) / 50000000000000000000)
def block516S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block516V (y : ℝ) : ℝ :=
  ratPotential block516W1 block516W2 block516W3 block516W4 block516S1 block516S2 block516S3 block516S4 y

def block516LeftParamsCertificate : Bool :=
  allBoxesSameParams block516LeftBoxes block516W1 block516W2 block516W3 block516W4 block516S1 block516S2 block516S3 block516S4

theorem block516LeftParamsCertificate_eq_true :
    block516LeftParamsCertificate = true := by
  native_decide

theorem block516_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block516LeftL : ℝ) (block516LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block516S1 : ℝ))
    (hy2ne : y ≠ (block516S2 : ℝ))
    (hy3ne : y ≠ (block516S3 : ℝ))
    (hy4ne : y ≠ (block516S4 : ℝ)) :
    0 < block516V y := by
  have hcert := block516LeftCertificate_eq_true
  unfold block516LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block516LeftBoxes) (lo := block516LeftL) (hi := block516LeftR)
    (w1 := block516W1) (w2 := block516W2) (w3 := block516W3) (w4 := block516W4)
    (s1 := block516S1) (s2 := block516S2) (s3 := block516S3) (s4 := block516S4)
    hboxes hcover block516LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block516RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block516RightChunk000 block516W1 block516W2 block516W3 block516W4 block516S1 block516S2 block516S3 block516S4

theorem block516RightChunk000ParamsCertificate_eq_true :
    block516RightChunk000ParamsCertificate = true := by
  native_decide

theorem block516_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block516RightChunk000L : ℝ) (block516RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block516S1 : ℝ))
    (hy2ne : y ≠ (block516S2 : ℝ))
    (hy3ne : y ≠ (block516S3 : ℝ))
    (hy4ne : y ≠ (block516S4 : ℝ)) :
    0 < block516V y := by
  have hcert := block516RightChunk000Certificate_eq_true
  unfold block516RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block516RightChunk000) (lo := block516RightChunk000L) (hi := block516RightChunk000R)
    (w1 := block516W1) (w2 := block516W2) (w3 := block516W3) (w4 := block516W4)
    (s1 := block516S1) (s2 := block516S2) (s3 := block516S3) (s4 := block516S4)
    hboxes hcover block516RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block516_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block516RightL : ℝ) (block516RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block516S1 : ℝ))
    (hy2ne : y ≠ (block516S2 : ℝ))
    (hy3ne : y ≠ (block516S3 : ℝ))
    (hy4ne : y ≠ (block516S4 : ℝ)) :
    0 < block516V y := by
  have hL : (block516RightChunk000L : ℝ) = (block516RightL : ℝ) := by
    norm_num [block516RightChunk000L, block516RightL]
  have hR : (block516RightChunk000R : ℝ) = (block516RightR : ℝ) := by
    norm_num [block516RightChunk000R, block516RightR]
  have hyc : y ∈ Icc (block516RightChunk000L : ℝ) (block516RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block516_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block516_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block516LeftL : ℝ) (block516LeftR : ℝ) →
    y ≠ 0 → y ≠ (block516S1 : ℝ) → y ≠ (block516S2 : ℝ) →
    y ≠ (block516S3 : ℝ) → y ≠ (block516S4 : ℝ) → 0 < block516V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block516RightL : ℝ) (block516RightR : ℝ) →
    y ≠ 0 → y ≠ (block516S1 : ℝ) → y ≠ (block516S2 : ℝ) →
    y ≠ (block516S3 : ℝ) → y ≠ (block516S4 : ℝ) → 0 < block516V y)

theorem block516_reallog_certificate_proof :
    block516_reallog_certificate := by
  exact ⟨block516_left_V_pos, block516_right_V_pos⟩

end Block516
end M1817475
end Erdos1038Lean
