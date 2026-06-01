import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block521

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block521

open Set

def block521W1 : Rat := ((10431626136340999 : Rat) / 25000000000000000)
def block521W2 : Rat := (0 : Rat)
def block521W3 : Rat := ((8975658524629011 : Rat) / 20000000000000000)
def block521W4 : Rat := (0 : Rat)
def block521S1 : Rat := ((18174751 : Rat) / 10000000)
def block521S2 : Rat := ((511587 : Rat) / 200000)
def block521S3 : Rat := ((129948472410714285881 : Rat) / 50000000000000000000)
def block521S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block521V (y : ℝ) : ℝ :=
  ratPotential block521W1 block521W2 block521W3 block521W4 block521S1 block521S2 block521S3 block521S4 y

def block521LeftParamsCertificate : Bool :=
  allBoxesSameParams block521LeftBoxes block521W1 block521W2 block521W3 block521W4 block521S1 block521S2 block521S3 block521S4

theorem block521LeftParamsCertificate_eq_true :
    block521LeftParamsCertificate = true := by
  native_decide

theorem block521_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block521LeftL : ℝ) (block521LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block521S1 : ℝ))
    (hy2ne : y ≠ (block521S2 : ℝ))
    (hy3ne : y ≠ (block521S3 : ℝ))
    (hy4ne : y ≠ (block521S4 : ℝ)) :
    0 < block521V y := by
  have hcert := block521LeftCertificate_eq_true
  unfold block521LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block521LeftBoxes) (lo := block521LeftL) (hi := block521LeftR)
    (w1 := block521W1) (w2 := block521W2) (w3 := block521W3) (w4 := block521W4)
    (s1 := block521S1) (s2 := block521S2) (s3 := block521S3) (s4 := block521S4)
    hboxes hcover block521LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block521RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block521RightChunk000 block521W1 block521W2 block521W3 block521W4 block521S1 block521S2 block521S3 block521S4

theorem block521RightChunk000ParamsCertificate_eq_true :
    block521RightChunk000ParamsCertificate = true := by
  native_decide

theorem block521_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block521RightChunk000L : ℝ) (block521RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block521S1 : ℝ))
    (hy2ne : y ≠ (block521S2 : ℝ))
    (hy3ne : y ≠ (block521S3 : ℝ))
    (hy4ne : y ≠ (block521S4 : ℝ)) :
    0 < block521V y := by
  have hcert := block521RightChunk000Certificate_eq_true
  unfold block521RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block521RightChunk000) (lo := block521RightChunk000L) (hi := block521RightChunk000R)
    (w1 := block521W1) (w2 := block521W2) (w3 := block521W3) (w4 := block521W4)
    (s1 := block521S1) (s2 := block521S2) (s3 := block521S3) (s4 := block521S4)
    hboxes hcover block521RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block521_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block521RightL : ℝ) (block521RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block521S1 : ℝ))
    (hy2ne : y ≠ (block521S2 : ℝ))
    (hy3ne : y ≠ (block521S3 : ℝ))
    (hy4ne : y ≠ (block521S4 : ℝ)) :
    0 < block521V y := by
  have hL : (block521RightChunk000L : ℝ) = (block521RightL : ℝ) := by
    norm_num [block521RightChunk000L, block521RightL]
  have hR : (block521RightChunk000R : ℝ) = (block521RightR : ℝ) := by
    norm_num [block521RightChunk000R, block521RightR]
  have hyc : y ∈ Icc (block521RightChunk000L : ℝ) (block521RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block521_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block521_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block521LeftL : ℝ) (block521LeftR : ℝ) →
    y ≠ 0 → y ≠ (block521S1 : ℝ) → y ≠ (block521S2 : ℝ) →
    y ≠ (block521S3 : ℝ) → y ≠ (block521S4 : ℝ) → 0 < block521V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block521RightL : ℝ) (block521RightR : ℝ) →
    y ≠ 0 → y ≠ (block521S1 : ℝ) → y ≠ (block521S2 : ℝ) →
    y ≠ (block521S3 : ℝ) → y ≠ (block521S4 : ℝ) → 0 < block521V y)

theorem block521_reallog_certificate_proof :
    block521_reallog_certificate := by
  exact ⟨block521_left_V_pos, block521_right_V_pos⟩

end Block521
end M1817475
end Erdos1038Lean
