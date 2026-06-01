import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block075

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block075

open Set

def block075W1 : Rat := ((31972600694252593 : Rat) / 10000000000000000)
def block075W2 : Rat := (0 : Rat)
def block075W3 : Rat := (0 : Rat)
def block075W4 : Rat := ((771379310626501 : Rat) / 3125000000000000)
def block075S1 : Rat := ((18174751 : Rat) / 10000000)
def block075S2 : Rat := ((511587 : Rat) / 200000)
def block075S3 : Rat := ((107000619 : Rat) / 40000000)
def block075S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block075V (y : ℝ) : ℝ :=
  ratPotential block075W1 block075W2 block075W3 block075W4 block075S1 block075S2 block075S3 block075S4 y

def block075LeftParamsCertificate : Bool :=
  allBoxesSameParams block075LeftBoxes block075W1 block075W2 block075W3 block075W4 block075S1 block075S2 block075S3 block075S4

theorem block075LeftParamsCertificate_eq_true :
    block075LeftParamsCertificate = true := by
  native_decide

theorem block075_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block075LeftL : ℝ) (block075LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block075S1 : ℝ))
    (hy2ne : y ≠ (block075S2 : ℝ))
    (hy3ne : y ≠ (block075S3 : ℝ))
    (hy4ne : y ≠ (block075S4 : ℝ)) :
    0 < block075V y := by
  have hcert := block075LeftCertificate_eq_true
  unfold block075LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block075LeftBoxes) (lo := block075LeftL) (hi := block075LeftR)
    (w1 := block075W1) (w2 := block075W2) (w3 := block075W3) (w4 := block075W4)
    (s1 := block075S1) (s2 := block075S2) (s3 := block075S3) (s4 := block075S4)
    hboxes hcover block075LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block075RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block075RightChunk000 block075W1 block075W2 block075W3 block075W4 block075S1 block075S2 block075S3 block075S4

theorem block075RightChunk000ParamsCertificate_eq_true :
    block075RightChunk000ParamsCertificate = true := by
  native_decide

theorem block075_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block075RightChunk000L : ℝ) (block075RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block075S1 : ℝ))
    (hy2ne : y ≠ (block075S2 : ℝ))
    (hy3ne : y ≠ (block075S3 : ℝ))
    (hy4ne : y ≠ (block075S4 : ℝ)) :
    0 < block075V y := by
  have hcert := block075RightChunk000Certificate_eq_true
  unfold block075RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block075RightChunk000) (lo := block075RightChunk000L) (hi := block075RightChunk000R)
    (w1 := block075W1) (w2 := block075W2) (w3 := block075W3) (w4 := block075W4)
    (s1 := block075S1) (s2 := block075S2) (s3 := block075S3) (s4 := block075S4)
    hboxes hcover block075RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block075_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block075RightL : ℝ) (block075RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block075S1 : ℝ))
    (hy2ne : y ≠ (block075S2 : ℝ))
    (hy3ne : y ≠ (block075S3 : ℝ))
    (hy4ne : y ≠ (block075S4 : ℝ)) :
    0 < block075V y := by
  have hL : (block075RightChunk000L : ℝ) = (block075RightL : ℝ) := by
    norm_num [block075RightChunk000L, block075RightL]
  have hR : (block075RightChunk000R : ℝ) = (block075RightR : ℝ) := by
    norm_num [block075RightChunk000R, block075RightR]
  have hyc : y ∈ Icc (block075RightChunk000L : ℝ) (block075RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block075_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block075_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block075LeftL : ℝ) (block075LeftR : ℝ) →
    y ≠ 0 → y ≠ (block075S1 : ℝ) → y ≠ (block075S2 : ℝ) →
    y ≠ (block075S3 : ℝ) → y ≠ (block075S4 : ℝ) → 0 < block075V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block075RightL : ℝ) (block075RightR : ℝ) →
    y ≠ 0 → y ≠ (block075S1 : ℝ) → y ≠ (block075S2 : ℝ) →
    y ≠ (block075S3 : ℝ) → y ≠ (block075S4 : ℝ) → 0 < block075V y)

theorem block075_reallog_certificate_proof :
    block075_reallog_certificate := by
  exact ⟨block075_left_V_pos, block075_right_V_pos⟩

end Block075
end M1817475
end Erdos1038Lean
