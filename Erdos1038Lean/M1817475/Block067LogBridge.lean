import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block067

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block067

open Set

def block067W1 : Rat := ((6019586609647189 : Rat) / 2000000000000000)
def block067W2 : Rat := (0 : Rat)
def block067W3 : Rat := (0 : Rat)
def block067W4 : Rat := ((25422527409187573 : Rat) / 100000000000000000)
def block067S1 : Rat := ((18174751 : Rat) / 10000000)
def block067S2 : Rat := ((511587 : Rat) / 200000)
def block067S3 : Rat := ((107000619 : Rat) / 40000000)
def block067S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block067V (y : ℝ) : ℝ :=
  ratPotential block067W1 block067W2 block067W3 block067W4 block067S1 block067S2 block067S3 block067S4 y

def block067LeftParamsCertificate : Bool :=
  allBoxesSameParams block067LeftBoxes block067W1 block067W2 block067W3 block067W4 block067S1 block067S2 block067S3 block067S4

theorem block067LeftParamsCertificate_eq_true :
    block067LeftParamsCertificate = true := by
  native_decide

theorem block067_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block067LeftL : ℝ) (block067LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block067S1 : ℝ))
    (hy2ne : y ≠ (block067S2 : ℝ))
    (hy3ne : y ≠ (block067S3 : ℝ))
    (hy4ne : y ≠ (block067S4 : ℝ)) :
    0 < block067V y := by
  have hcert := block067LeftCertificate_eq_true
  unfold block067LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block067LeftBoxes) (lo := block067LeftL) (hi := block067LeftR)
    (w1 := block067W1) (w2 := block067W2) (w3 := block067W3) (w4 := block067W4)
    (s1 := block067S1) (s2 := block067S2) (s3 := block067S3) (s4 := block067S4)
    hboxes hcover block067LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block067RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block067RightChunk000 block067W1 block067W2 block067W3 block067W4 block067S1 block067S2 block067S3 block067S4

theorem block067RightChunk000ParamsCertificate_eq_true :
    block067RightChunk000ParamsCertificate = true := by
  native_decide

theorem block067_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block067RightChunk000L : ℝ) (block067RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block067S1 : ℝ))
    (hy2ne : y ≠ (block067S2 : ℝ))
    (hy3ne : y ≠ (block067S3 : ℝ))
    (hy4ne : y ≠ (block067S4 : ℝ)) :
    0 < block067V y := by
  have hcert := block067RightChunk000Certificate_eq_true
  unfold block067RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block067RightChunk000) (lo := block067RightChunk000L) (hi := block067RightChunk000R)
    (w1 := block067W1) (w2 := block067W2) (w3 := block067W3) (w4 := block067W4)
    (s1 := block067S1) (s2 := block067S2) (s3 := block067S3) (s4 := block067S4)
    hboxes hcover block067RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block067_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block067RightL : ℝ) (block067RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block067S1 : ℝ))
    (hy2ne : y ≠ (block067S2 : ℝ))
    (hy3ne : y ≠ (block067S3 : ℝ))
    (hy4ne : y ≠ (block067S4 : ℝ)) :
    0 < block067V y := by
  have hL : (block067RightChunk000L : ℝ) = (block067RightL : ℝ) := by
    norm_num [block067RightChunk000L, block067RightL]
  have hR : (block067RightChunk000R : ℝ) = (block067RightR : ℝ) := by
    norm_num [block067RightChunk000R, block067RightR]
  have hyc : y ∈ Icc (block067RightChunk000L : ℝ) (block067RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block067_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block067_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block067LeftL : ℝ) (block067LeftR : ℝ) →
    y ≠ 0 → y ≠ (block067S1 : ℝ) → y ≠ (block067S2 : ℝ) →
    y ≠ (block067S3 : ℝ) → y ≠ (block067S4 : ℝ) → 0 < block067V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block067RightL : ℝ) (block067RightR : ℝ) →
    y ≠ 0 → y ≠ (block067S1 : ℝ) → y ≠ (block067S2 : ℝ) →
    y ≠ (block067S3 : ℝ) → y ≠ (block067S4 : ℝ) → 0 < block067V y)

theorem block067_reallog_certificate_proof :
    block067_reallog_certificate := by
  exact ⟨block067_left_V_pos, block067_right_V_pos⟩

end Block067
end M1817475
end Erdos1038Lean
