import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block471

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block471

open Set

def block471W1 : Rat := ((2694498337383371 : Rat) / 5000000000000000)
def block471W2 : Rat := (0 : Rat)
def block471W3 : Rat := ((18172713842935667 : Rat) / 50000000000000000)
def block471W4 : Rat := ((5053887668700801 : Rat) / 100000000000000000)
def block471S1 : Rat := ((18174751 : Rat) / 10000000)
def block471S2 : Rat := ((511587 : Rat) / 200000)
def block471S3 : Rat := ((130925927767857142981 : Rat) / 50000000000000000000)
def block471S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block471V (y : ℝ) : ℝ :=
  ratPotential block471W1 block471W2 block471W3 block471W4 block471S1 block471S2 block471S3 block471S4 y

def block471LeftParamsCertificate : Bool :=
  allBoxesSameParams block471LeftBoxes block471W1 block471W2 block471W3 block471W4 block471S1 block471S2 block471S3 block471S4

theorem block471LeftParamsCertificate_eq_true :
    block471LeftParamsCertificate = true := by
  native_decide

theorem block471_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block471LeftL : ℝ) (block471LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block471S1 : ℝ))
    (hy2ne : y ≠ (block471S2 : ℝ))
    (hy3ne : y ≠ (block471S3 : ℝ))
    (hy4ne : y ≠ (block471S4 : ℝ)) :
    0 < block471V y := by
  have hcert := block471LeftCertificate_eq_true
  unfold block471LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block471LeftBoxes) (lo := block471LeftL) (hi := block471LeftR)
    (w1 := block471W1) (w2 := block471W2) (w3 := block471W3) (w4 := block471W4)
    (s1 := block471S1) (s2 := block471S2) (s3 := block471S3) (s4 := block471S4)
    hboxes hcover block471LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block471RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block471RightChunk000 block471W1 block471W2 block471W3 block471W4 block471S1 block471S2 block471S3 block471S4

theorem block471RightChunk000ParamsCertificate_eq_true :
    block471RightChunk000ParamsCertificate = true := by
  native_decide

theorem block471_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block471RightChunk000L : ℝ) (block471RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block471S1 : ℝ))
    (hy2ne : y ≠ (block471S2 : ℝ))
    (hy3ne : y ≠ (block471S3 : ℝ))
    (hy4ne : y ≠ (block471S4 : ℝ)) :
    0 < block471V y := by
  have hcert := block471RightChunk000Certificate_eq_true
  unfold block471RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block471RightChunk000) (lo := block471RightChunk000L) (hi := block471RightChunk000R)
    (w1 := block471W1) (w2 := block471W2) (w3 := block471W3) (w4 := block471W4)
    (s1 := block471S1) (s2 := block471S2) (s3 := block471S3) (s4 := block471S4)
    hboxes hcover block471RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block471_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block471RightL : ℝ) (block471RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block471S1 : ℝ))
    (hy2ne : y ≠ (block471S2 : ℝ))
    (hy3ne : y ≠ (block471S3 : ℝ))
    (hy4ne : y ≠ (block471S4 : ℝ)) :
    0 < block471V y := by
  have hL : (block471RightChunk000L : ℝ) = (block471RightL : ℝ) := by
    norm_num [block471RightChunk000L, block471RightL]
  have hR : (block471RightChunk000R : ℝ) = (block471RightR : ℝ) := by
    norm_num [block471RightChunk000R, block471RightR]
  have hyc : y ∈ Icc (block471RightChunk000L : ℝ) (block471RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block471_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block471_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block471LeftL : ℝ) (block471LeftR : ℝ) →
    y ≠ 0 → y ≠ (block471S1 : ℝ) → y ≠ (block471S2 : ℝ) →
    y ≠ (block471S3 : ℝ) → y ≠ (block471S4 : ℝ) → 0 < block471V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block471RightL : ℝ) (block471RightR : ℝ) →
    y ≠ 0 → y ≠ (block471S1 : ℝ) → y ≠ (block471S2 : ℝ) →
    y ≠ (block471S3 : ℝ) → y ≠ (block471S4 : ℝ) → 0 < block471V y)

theorem block471_reallog_certificate_proof :
    block471_reallog_certificate := by
  exact ⟨block471_left_V_pos, block471_right_V_pos⟩

end Block471
end M1817475
end Erdos1038Lean
