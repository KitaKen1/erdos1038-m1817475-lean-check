import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block456

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block456

open Set

def block456W1 : Rat := ((5804337708371161 : Rat) / 10000000000000000)
def block456W2 : Rat := (0 : Rat)
def block456W3 : Rat := ((6824538829024911 : Rat) / 20000000000000000)
def block456W4 : Rat := ((1570169186490009 : Rat) / 25000000000000000)
def block456S1 : Rat := ((18174751 : Rat) / 10000000)
def block456S2 : Rat := ((511587 : Rat) / 200000)
def block456S3 : Rat := ((131219164375000000111 : Rat) / 50000000000000000000)
def block456S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block456V (y : ℝ) : ℝ :=
  ratPotential block456W1 block456W2 block456W3 block456W4 block456S1 block456S2 block456S3 block456S4 y

def block456LeftParamsCertificate : Bool :=
  allBoxesSameParams block456LeftBoxes block456W1 block456W2 block456W3 block456W4 block456S1 block456S2 block456S3 block456S4

theorem block456LeftParamsCertificate_eq_true :
    block456LeftParamsCertificate = true := by
  native_decide

theorem block456_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block456LeftL : ℝ) (block456LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block456S1 : ℝ))
    (hy2ne : y ≠ (block456S2 : ℝ))
    (hy3ne : y ≠ (block456S3 : ℝ))
    (hy4ne : y ≠ (block456S4 : ℝ)) :
    0 < block456V y := by
  have hcert := block456LeftCertificate_eq_true
  unfold block456LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block456LeftBoxes) (lo := block456LeftL) (hi := block456LeftR)
    (w1 := block456W1) (w2 := block456W2) (w3 := block456W3) (w4 := block456W4)
    (s1 := block456S1) (s2 := block456S2) (s3 := block456S3) (s4 := block456S4)
    hboxes hcover block456LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block456RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block456RightChunk000 block456W1 block456W2 block456W3 block456W4 block456S1 block456S2 block456S3 block456S4

theorem block456RightChunk000ParamsCertificate_eq_true :
    block456RightChunk000ParamsCertificate = true := by
  native_decide

theorem block456_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block456RightChunk000L : ℝ) (block456RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block456S1 : ℝ))
    (hy2ne : y ≠ (block456S2 : ℝ))
    (hy3ne : y ≠ (block456S3 : ℝ))
    (hy4ne : y ≠ (block456S4 : ℝ)) :
    0 < block456V y := by
  have hcert := block456RightChunk000Certificate_eq_true
  unfold block456RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block456RightChunk000) (lo := block456RightChunk000L) (hi := block456RightChunk000R)
    (w1 := block456W1) (w2 := block456W2) (w3 := block456W3) (w4 := block456W4)
    (s1 := block456S1) (s2 := block456S2) (s3 := block456S3) (s4 := block456S4)
    hboxes hcover block456RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block456_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block456RightL : ℝ) (block456RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block456S1 : ℝ))
    (hy2ne : y ≠ (block456S2 : ℝ))
    (hy3ne : y ≠ (block456S3 : ℝ))
    (hy4ne : y ≠ (block456S4 : ℝ)) :
    0 < block456V y := by
  have hL : (block456RightChunk000L : ℝ) = (block456RightL : ℝ) := by
    norm_num [block456RightChunk000L, block456RightL]
  have hR : (block456RightChunk000R : ℝ) = (block456RightR : ℝ) := by
    norm_num [block456RightChunk000R, block456RightR]
  have hyc : y ∈ Icc (block456RightChunk000L : ℝ) (block456RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block456_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block456_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block456LeftL : ℝ) (block456LeftR : ℝ) →
    y ≠ 0 → y ≠ (block456S1 : ℝ) → y ≠ (block456S2 : ℝ) →
    y ≠ (block456S3 : ℝ) → y ≠ (block456S4 : ℝ) → 0 < block456V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block456RightL : ℝ) (block456RightR : ℝ) →
    y ≠ 0 → y ≠ (block456S1 : ℝ) → y ≠ (block456S2 : ℝ) →
    y ≠ (block456S3 : ℝ) → y ≠ (block456S4 : ℝ) → 0 < block456V y)

theorem block456_reallog_certificate_proof :
    block456_reallog_certificate := by
  exact ⟨block456_left_V_pos, block456_right_V_pos⟩

end Block456
end M1817475
end Erdos1038Lean
