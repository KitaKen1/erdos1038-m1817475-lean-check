import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block125

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block125

open Set

def block125W1 : Rat := ((2571554286619753 : Rat) / 1000000000000000)
def block125W2 : Rat := (0 : Rat)
def block125W3 : Rat := ((9772395112063513 : Rat) / 100000000000000000)
def block125W4 : Rat := ((1449190589736953 : Rat) / 10000000000000000)
def block125S1 : Rat := ((18174751 : Rat) / 10000000)
def block125S2 : Rat := ((511587 : Rat) / 200000)
def block125S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block125S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block125V (y : ℝ) : ℝ :=
  ratPotential block125W1 block125W2 block125W3 block125W4 block125S1 block125S2 block125S3 block125S4 y

def block125LeftParamsCertificate : Bool :=
  allBoxesSameParams block125LeftBoxes block125W1 block125W2 block125W3 block125W4 block125S1 block125S2 block125S3 block125S4

theorem block125LeftParamsCertificate_eq_true :
    block125LeftParamsCertificate = true := by
  native_decide

theorem block125_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block125LeftL : ℝ) (block125LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block125S1 : ℝ))
    (hy2ne : y ≠ (block125S2 : ℝ))
    (hy3ne : y ≠ (block125S3 : ℝ))
    (hy4ne : y ≠ (block125S4 : ℝ)) :
    0 < block125V y := by
  have hcert := block125LeftCertificate_eq_true
  unfold block125LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block125LeftBoxes) (lo := block125LeftL) (hi := block125LeftR)
    (w1 := block125W1) (w2 := block125W2) (w3 := block125W3) (w4 := block125W4)
    (s1 := block125S1) (s2 := block125S2) (s3 := block125S3) (s4 := block125S4)
    hboxes hcover block125LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block125RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block125RightChunk000 block125W1 block125W2 block125W3 block125W4 block125S1 block125S2 block125S3 block125S4

theorem block125RightChunk000ParamsCertificate_eq_true :
    block125RightChunk000ParamsCertificate = true := by
  native_decide

theorem block125_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block125RightChunk000L : ℝ) (block125RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block125S1 : ℝ))
    (hy2ne : y ≠ (block125S2 : ℝ))
    (hy3ne : y ≠ (block125S3 : ℝ))
    (hy4ne : y ≠ (block125S4 : ℝ)) :
    0 < block125V y := by
  have hcert := block125RightChunk000Certificate_eq_true
  unfold block125RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block125RightChunk000) (lo := block125RightChunk000L) (hi := block125RightChunk000R)
    (w1 := block125W1) (w2 := block125W2) (w3 := block125W3) (w4 := block125W4)
    (s1 := block125S1) (s2 := block125S2) (s3 := block125S3) (s4 := block125S4)
    hboxes hcover block125RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block125_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block125RightL : ℝ) (block125RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block125S1 : ℝ))
    (hy2ne : y ≠ (block125S2 : ℝ))
    (hy3ne : y ≠ (block125S3 : ℝ))
    (hy4ne : y ≠ (block125S4 : ℝ)) :
    0 < block125V y := by
  have hL : (block125RightChunk000L : ℝ) = (block125RightL : ℝ) := by
    norm_num [block125RightChunk000L, block125RightL]
  have hR : (block125RightChunk000R : ℝ) = (block125RightR : ℝ) := by
    norm_num [block125RightChunk000R, block125RightR]
  have hyc : y ∈ Icc (block125RightChunk000L : ℝ) (block125RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block125_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block125_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block125LeftL : ℝ) (block125LeftR : ℝ) →
    y ≠ 0 → y ≠ (block125S1 : ℝ) → y ≠ (block125S2 : ℝ) →
    y ≠ (block125S3 : ℝ) → y ≠ (block125S4 : ℝ) → 0 < block125V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block125RightL : ℝ) (block125RightR : ℝ) →
    y ≠ 0 → y ≠ (block125S1 : ℝ) → y ≠ (block125S2 : ℝ) →
    y ≠ (block125S3 : ℝ) → y ≠ (block125S4 : ℝ) → 0 < block125V y)

theorem block125_reallog_certificate_proof :
    block125_reallog_certificate := by
  exact ⟨block125_left_V_pos, block125_right_V_pos⟩

end Block125
end M1817475
end Erdos1038Lean
