import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block544

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block544

open Set

def block544W1 : Rat := ((9840990638176729 : Rat) / 25000000000000000)
def block544W2 : Rat := (0 : Rat)
def block544W3 : Rat := ((22875821542112573 : Rat) / 50000000000000000)
def block544W4 : Rat := (0 : Rat)
def block544S1 : Rat := ((18174751 : Rat) / 10000000)
def block544S2 : Rat := ((511587 : Rat) / 200000)
def block544S3 : Rat := ((25899768589285714323 : Rat) / 10000000000000000000)
def block544S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block544V (y : ℝ) : ℝ :=
  ratPotential block544W1 block544W2 block544W3 block544W4 block544S1 block544S2 block544S3 block544S4 y

def block544LeftParamsCertificate : Bool :=
  allBoxesSameParams block544LeftBoxes block544W1 block544W2 block544W3 block544W4 block544S1 block544S2 block544S3 block544S4

theorem block544LeftParamsCertificate_eq_true :
    block544LeftParamsCertificate = true := by
  native_decide

theorem block544_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block544LeftL : ℝ) (block544LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block544S1 : ℝ))
    (hy2ne : y ≠ (block544S2 : ℝ))
    (hy3ne : y ≠ (block544S3 : ℝ))
    (hy4ne : y ≠ (block544S4 : ℝ)) :
    0 < block544V y := by
  have hcert := block544LeftCertificate_eq_true
  unfold block544LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block544LeftBoxes) (lo := block544LeftL) (hi := block544LeftR)
    (w1 := block544W1) (w2 := block544W2) (w3 := block544W3) (w4 := block544W4)
    (s1 := block544S1) (s2 := block544S2) (s3 := block544S3) (s4 := block544S4)
    hboxes hcover block544LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block544RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block544RightChunk000 block544W1 block544W2 block544W3 block544W4 block544S1 block544S2 block544S3 block544S4

theorem block544RightChunk000ParamsCertificate_eq_true :
    block544RightChunk000ParamsCertificate = true := by
  native_decide

theorem block544_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block544RightChunk000L : ℝ) (block544RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block544S1 : ℝ))
    (hy2ne : y ≠ (block544S2 : ℝ))
    (hy3ne : y ≠ (block544S3 : ℝ))
    (hy4ne : y ≠ (block544S4 : ℝ)) :
    0 < block544V y := by
  have hcert := block544RightChunk000Certificate_eq_true
  unfold block544RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block544RightChunk000) (lo := block544RightChunk000L) (hi := block544RightChunk000R)
    (w1 := block544W1) (w2 := block544W2) (w3 := block544W3) (w4 := block544W4)
    (s1 := block544S1) (s2 := block544S2) (s3 := block544S3) (s4 := block544S4)
    hboxes hcover block544RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block544_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block544RightL : ℝ) (block544RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block544S1 : ℝ))
    (hy2ne : y ≠ (block544S2 : ℝ))
    (hy3ne : y ≠ (block544S3 : ℝ))
    (hy4ne : y ≠ (block544S4 : ℝ)) :
    0 < block544V y := by
  have hL : (block544RightChunk000L : ℝ) = (block544RightL : ℝ) := by
    norm_num [block544RightChunk000L, block544RightL]
  have hR : (block544RightChunk000R : ℝ) = (block544RightR : ℝ) := by
    norm_num [block544RightChunk000R, block544RightR]
  have hyc : y ∈ Icc (block544RightChunk000L : ℝ) (block544RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block544_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block544_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block544LeftL : ℝ) (block544LeftR : ℝ) →
    y ≠ 0 → y ≠ (block544S1 : ℝ) → y ≠ (block544S2 : ℝ) →
    y ≠ (block544S3 : ℝ) → y ≠ (block544S4 : ℝ) → 0 < block544V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block544RightL : ℝ) (block544RightR : ℝ) →
    y ≠ 0 → y ≠ (block544S1 : ℝ) → y ≠ (block544S2 : ℝ) →
    y ≠ (block544S3 : ℝ) → y ≠ (block544S4 : ℝ) → 0 < block544V y)

theorem block544_reallog_certificate_proof :
    block544_reallog_certificate := by
  exact ⟨block544_left_V_pos, block544_right_V_pos⟩

end Block544
end M1817475
end Erdos1038Lean
