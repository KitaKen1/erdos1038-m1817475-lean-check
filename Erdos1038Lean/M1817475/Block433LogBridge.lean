import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block433

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block433

open Set

def block433W1 : Rat := ((101139995420191 : Rat) / 156250000000000)
def block433W2 : Rat := (0 : Rat)
def block433W3 : Rat := ((3114415516085367 : Rat) / 10000000000000000)
def block433W4 : Rat := ((62474248243177 : Rat) / 800000000000000)
def block433S1 : Rat := ((18174751 : Rat) / 10000000)
def block433S2 : Rat := ((511587 : Rat) / 200000)
def block433S3 : Rat := ((131668793839285714377 : Rat) / 50000000000000000000)
def block433S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block433V (y : ℝ) : ℝ :=
  ratPotential block433W1 block433W2 block433W3 block433W4 block433S1 block433S2 block433S3 block433S4 y

def block433LeftParamsCertificate : Bool :=
  allBoxesSameParams block433LeftBoxes block433W1 block433W2 block433W3 block433W4 block433S1 block433S2 block433S3 block433S4

theorem block433LeftParamsCertificate_eq_true :
    block433LeftParamsCertificate = true := by
  native_decide

theorem block433_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block433LeftL : ℝ) (block433LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block433S1 : ℝ))
    (hy2ne : y ≠ (block433S2 : ℝ))
    (hy3ne : y ≠ (block433S3 : ℝ))
    (hy4ne : y ≠ (block433S4 : ℝ)) :
    0 < block433V y := by
  have hcert := block433LeftCertificate_eq_true
  unfold block433LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block433LeftBoxes) (lo := block433LeftL) (hi := block433LeftR)
    (w1 := block433W1) (w2 := block433W2) (w3 := block433W3) (w4 := block433W4)
    (s1 := block433S1) (s2 := block433S2) (s3 := block433S3) (s4 := block433S4)
    hboxes hcover block433LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block433RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block433RightChunk000 block433W1 block433W2 block433W3 block433W4 block433S1 block433S2 block433S3 block433S4

theorem block433RightChunk000ParamsCertificate_eq_true :
    block433RightChunk000ParamsCertificate = true := by
  native_decide

theorem block433_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block433RightChunk000L : ℝ) (block433RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block433S1 : ℝ))
    (hy2ne : y ≠ (block433S2 : ℝ))
    (hy3ne : y ≠ (block433S3 : ℝ))
    (hy4ne : y ≠ (block433S4 : ℝ)) :
    0 < block433V y := by
  have hcert := block433RightChunk000Certificate_eq_true
  unfold block433RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block433RightChunk000) (lo := block433RightChunk000L) (hi := block433RightChunk000R)
    (w1 := block433W1) (w2 := block433W2) (w3 := block433W3) (w4 := block433W4)
    (s1 := block433S1) (s2 := block433S2) (s3 := block433S3) (s4 := block433S4)
    hboxes hcover block433RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block433_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block433RightL : ℝ) (block433RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block433S1 : ℝ))
    (hy2ne : y ≠ (block433S2 : ℝ))
    (hy3ne : y ≠ (block433S3 : ℝ))
    (hy4ne : y ≠ (block433S4 : ℝ)) :
    0 < block433V y := by
  have hL : (block433RightChunk000L : ℝ) = (block433RightL : ℝ) := by
    norm_num [block433RightChunk000L, block433RightL]
  have hR : (block433RightChunk000R : ℝ) = (block433RightR : ℝ) := by
    norm_num [block433RightChunk000R, block433RightR]
  have hyc : y ∈ Icc (block433RightChunk000L : ℝ) (block433RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block433_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block433_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block433LeftL : ℝ) (block433LeftR : ℝ) →
    y ≠ 0 → y ≠ (block433S1 : ℝ) → y ≠ (block433S2 : ℝ) →
    y ≠ (block433S3 : ℝ) → y ≠ (block433S4 : ℝ) → 0 < block433V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block433RightL : ℝ) (block433RightR : ℝ) →
    y ≠ 0 → y ≠ (block433S1 : ℝ) → y ≠ (block433S2 : ℝ) →
    y ≠ (block433S3 : ℝ) → y ≠ (block433S4 : ℝ) → 0 < block433V y)

theorem block433_reallog_certificate_proof :
    block433_reallog_certificate := by
  exact ⟨block433_left_V_pos, block433_right_V_pos⟩

end Block433
end M1817475
end Erdos1038Lean
