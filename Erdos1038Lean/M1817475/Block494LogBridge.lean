import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block494

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block494

open Set

def block494W1 : Rat := ((1192980069333117 : Rat) / 2500000000000000)
def block494W2 : Rat := (0 : Rat)
def block494W3 : Rat := ((40352988689973 : Rat) / 100000000000000)
def block494W4 : Rat := ((13433692143546571 : Rat) / 500000000000000000)
def block494S1 : Rat := ((18174751 : Rat) / 10000000)
def block494S2 : Rat := ((511587 : Rat) / 200000)
def block494S3 : Rat := ((26095259660714285743 : Rat) / 10000000000000000000)
def block494S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block494V (y : ℝ) : ℝ :=
  ratPotential block494W1 block494W2 block494W3 block494W4 block494S1 block494S2 block494S3 block494S4 y

def block494LeftParamsCertificate : Bool :=
  allBoxesSameParams block494LeftBoxes block494W1 block494W2 block494W3 block494W4 block494S1 block494S2 block494S3 block494S4

theorem block494LeftParamsCertificate_eq_true :
    block494LeftParamsCertificate = true := by
  native_decide

theorem block494_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block494LeftL : ℝ) (block494LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block494S1 : ℝ))
    (hy2ne : y ≠ (block494S2 : ℝ))
    (hy3ne : y ≠ (block494S3 : ℝ))
    (hy4ne : y ≠ (block494S4 : ℝ)) :
    0 < block494V y := by
  have hcert := block494LeftCertificate_eq_true
  unfold block494LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block494LeftBoxes) (lo := block494LeftL) (hi := block494LeftR)
    (w1 := block494W1) (w2 := block494W2) (w3 := block494W3) (w4 := block494W4)
    (s1 := block494S1) (s2 := block494S2) (s3 := block494S3) (s4 := block494S4)
    hboxes hcover block494LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block494RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block494RightChunk000 block494W1 block494W2 block494W3 block494W4 block494S1 block494S2 block494S3 block494S4

theorem block494RightChunk000ParamsCertificate_eq_true :
    block494RightChunk000ParamsCertificate = true := by
  native_decide

theorem block494_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block494RightChunk000L : ℝ) (block494RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block494S1 : ℝ))
    (hy2ne : y ≠ (block494S2 : ℝ))
    (hy3ne : y ≠ (block494S3 : ℝ))
    (hy4ne : y ≠ (block494S4 : ℝ)) :
    0 < block494V y := by
  have hcert := block494RightChunk000Certificate_eq_true
  unfold block494RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block494RightChunk000) (lo := block494RightChunk000L) (hi := block494RightChunk000R)
    (w1 := block494W1) (w2 := block494W2) (w3 := block494W3) (w4 := block494W4)
    (s1 := block494S1) (s2 := block494S2) (s3 := block494S3) (s4 := block494S4)
    hboxes hcover block494RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block494_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block494RightL : ℝ) (block494RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block494S1 : ℝ))
    (hy2ne : y ≠ (block494S2 : ℝ))
    (hy3ne : y ≠ (block494S3 : ℝ))
    (hy4ne : y ≠ (block494S4 : ℝ)) :
    0 < block494V y := by
  have hL : (block494RightChunk000L : ℝ) = (block494RightL : ℝ) := by
    norm_num [block494RightChunk000L, block494RightL]
  have hR : (block494RightChunk000R : ℝ) = (block494RightR : ℝ) := by
    norm_num [block494RightChunk000R, block494RightR]
  have hyc : y ∈ Icc (block494RightChunk000L : ℝ) (block494RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block494_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block494_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block494LeftL : ℝ) (block494LeftR : ℝ) →
    y ≠ 0 → y ≠ (block494S1 : ℝ) → y ≠ (block494S2 : ℝ) →
    y ≠ (block494S3 : ℝ) → y ≠ (block494S4 : ℝ) → 0 < block494V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block494RightL : ℝ) (block494RightR : ℝ) →
    y ≠ 0 → y ≠ (block494S1 : ℝ) → y ≠ (block494S2 : ℝ) →
    y ≠ (block494S3 : ℝ) → y ≠ (block494S4 : ℝ) → 0 < block494V y)

theorem block494_reallog_certificate_proof :
    block494_reallog_certificate := by
  exact ⟨block494_left_V_pos, block494_right_V_pos⟩

end Block494
end M1817475
end Erdos1038Lean
