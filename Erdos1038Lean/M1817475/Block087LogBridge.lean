import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block087

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block087

open Set

def block087W1 : Rat := ((3529443261091241 : Rat) / 1000000000000000)
def block087W2 : Rat := (0 : Rat)
def block087W3 : Rat := (0 : Rat)
def block087W4 : Rat := ((23473234300333737 : Rat) / 100000000000000000)
def block087S1 : Rat := ((18174751 : Rat) / 10000000)
def block087S2 : Rat := ((511587 : Rat) / 200000)
def block087S3 : Rat := ((107000619 : Rat) / 40000000)
def block087S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block087V (y : ℝ) : ℝ :=
  ratPotential block087W1 block087W2 block087W3 block087W4 block087S1 block087S2 block087S3 block087S4 y

def block087LeftParamsCertificate : Bool :=
  allBoxesSameParams block087LeftBoxes block087W1 block087W2 block087W3 block087W4 block087S1 block087S2 block087S3 block087S4

theorem block087LeftParamsCertificate_eq_true :
    block087LeftParamsCertificate = true := by
  native_decide

theorem block087_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block087LeftL : ℝ) (block087LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block087S1 : ℝ))
    (hy2ne : y ≠ (block087S2 : ℝ))
    (hy3ne : y ≠ (block087S3 : ℝ))
    (hy4ne : y ≠ (block087S4 : ℝ)) :
    0 < block087V y := by
  have hcert := block087LeftCertificate_eq_true
  unfold block087LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block087LeftBoxes) (lo := block087LeftL) (hi := block087LeftR)
    (w1 := block087W1) (w2 := block087W2) (w3 := block087W3) (w4 := block087W4)
    (s1 := block087S1) (s2 := block087S2) (s3 := block087S3) (s4 := block087S4)
    hboxes hcover block087LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block087RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block087RightChunk000 block087W1 block087W2 block087W3 block087W4 block087S1 block087S2 block087S3 block087S4

theorem block087RightChunk000ParamsCertificate_eq_true :
    block087RightChunk000ParamsCertificate = true := by
  native_decide

theorem block087_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block087RightChunk000L : ℝ) (block087RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block087S1 : ℝ))
    (hy2ne : y ≠ (block087S2 : ℝ))
    (hy3ne : y ≠ (block087S3 : ℝ))
    (hy4ne : y ≠ (block087S4 : ℝ)) :
    0 < block087V y := by
  have hcert := block087RightChunk000Certificate_eq_true
  unfold block087RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block087RightChunk000) (lo := block087RightChunk000L) (hi := block087RightChunk000R)
    (w1 := block087W1) (w2 := block087W2) (w3 := block087W3) (w4 := block087W4)
    (s1 := block087S1) (s2 := block087S2) (s3 := block087S3) (s4 := block087S4)
    hboxes hcover block087RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block087_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block087RightL : ℝ) (block087RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block087S1 : ℝ))
    (hy2ne : y ≠ (block087S2 : ℝ))
    (hy3ne : y ≠ (block087S3 : ℝ))
    (hy4ne : y ≠ (block087S4 : ℝ)) :
    0 < block087V y := by
  have hL : (block087RightChunk000L : ℝ) = (block087RightL : ℝ) := by
    norm_num [block087RightChunk000L, block087RightL]
  have hR : (block087RightChunk000R : ℝ) = (block087RightR : ℝ) := by
    norm_num [block087RightChunk000R, block087RightR]
  have hyc : y ∈ Icc (block087RightChunk000L : ℝ) (block087RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block087_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block087_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block087LeftL : ℝ) (block087LeftR : ℝ) →
    y ≠ 0 → y ≠ (block087S1 : ℝ) → y ≠ (block087S2 : ℝ) →
    y ≠ (block087S3 : ℝ) → y ≠ (block087S4 : ℝ) → 0 < block087V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block087RightL : ℝ) (block087RightR : ℝ) →
    y ≠ 0 → y ≠ (block087S1 : ℝ) → y ≠ (block087S2 : ℝ) →
    y ≠ (block087S3 : ℝ) → y ≠ (block087S4 : ℝ) → 0 < block087V y)

theorem block087_reallog_certificate_proof :
    block087_reallog_certificate := by
  exact ⟨block087_left_V_pos, block087_right_V_pos⟩

end Block087
end M1817475
end Erdos1038Lean
