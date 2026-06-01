import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block510

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block510

open Set

def block510W1 : Rat := ((4355166974113863 : Rat) / 10000000000000000)
def block510W2 : Rat := (0 : Rat)
def block510W3 : Rat := ((136417164977227 : Rat) / 312500000000000)
def block510W4 : Rat := ((31167304059536473 : Rat) / 5000000000000000000)
def block510S1 : Rat := ((18174751 : Rat) / 10000000)
def block510S2 : Rat := ((511587 : Rat) / 200000)
def block510S3 : Rat := ((130163512589285714443 : Rat) / 50000000000000000000)
def block510S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block510V (y : ℝ) : ℝ :=
  ratPotential block510W1 block510W2 block510W3 block510W4 block510S1 block510S2 block510S3 block510S4 y

def block510LeftParamsCertificate : Bool :=
  allBoxesSameParams block510LeftBoxes block510W1 block510W2 block510W3 block510W4 block510S1 block510S2 block510S3 block510S4

theorem block510LeftParamsCertificate_eq_true :
    block510LeftParamsCertificate = true := by
  native_decide

theorem block510_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block510LeftL : ℝ) (block510LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block510S1 : ℝ))
    (hy2ne : y ≠ (block510S2 : ℝ))
    (hy3ne : y ≠ (block510S3 : ℝ))
    (hy4ne : y ≠ (block510S4 : ℝ)) :
    0 < block510V y := by
  have hcert := block510LeftCertificate_eq_true
  unfold block510LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block510LeftBoxes) (lo := block510LeftL) (hi := block510LeftR)
    (w1 := block510W1) (w2 := block510W2) (w3 := block510W3) (w4 := block510W4)
    (s1 := block510S1) (s2 := block510S2) (s3 := block510S3) (s4 := block510S4)
    hboxes hcover block510LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block510RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block510RightChunk000 block510W1 block510W2 block510W3 block510W4 block510S1 block510S2 block510S3 block510S4

theorem block510RightChunk000ParamsCertificate_eq_true :
    block510RightChunk000ParamsCertificate = true := by
  native_decide

theorem block510_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block510RightChunk000L : ℝ) (block510RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block510S1 : ℝ))
    (hy2ne : y ≠ (block510S2 : ℝ))
    (hy3ne : y ≠ (block510S3 : ℝ))
    (hy4ne : y ≠ (block510S4 : ℝ)) :
    0 < block510V y := by
  have hcert := block510RightChunk000Certificate_eq_true
  unfold block510RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block510RightChunk000) (lo := block510RightChunk000L) (hi := block510RightChunk000R)
    (w1 := block510W1) (w2 := block510W2) (w3 := block510W3) (w4 := block510W4)
    (s1 := block510S1) (s2 := block510S2) (s3 := block510S3) (s4 := block510S4)
    hboxes hcover block510RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block510_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block510RightL : ℝ) (block510RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block510S1 : ℝ))
    (hy2ne : y ≠ (block510S2 : ℝ))
    (hy3ne : y ≠ (block510S3 : ℝ))
    (hy4ne : y ≠ (block510S4 : ℝ)) :
    0 < block510V y := by
  have hL : (block510RightChunk000L : ℝ) = (block510RightL : ℝ) := by
    norm_num [block510RightChunk000L, block510RightL]
  have hR : (block510RightChunk000R : ℝ) = (block510RightR : ℝ) := by
    norm_num [block510RightChunk000R, block510RightR]
  have hyc : y ∈ Icc (block510RightChunk000L : ℝ) (block510RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block510_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block510_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block510LeftL : ℝ) (block510LeftR : ℝ) →
    y ≠ 0 → y ≠ (block510S1 : ℝ) → y ≠ (block510S2 : ℝ) →
    y ≠ (block510S3 : ℝ) → y ≠ (block510S4 : ℝ) → 0 < block510V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block510RightL : ℝ) (block510RightR : ℝ) →
    y ≠ 0 → y ≠ (block510S1 : ℝ) → y ≠ (block510S2 : ℝ) →
    y ≠ (block510S3 : ℝ) → y ≠ (block510S4 : ℝ) → 0 < block510V y)

theorem block510_reallog_certificate_proof :
    block510_reallog_certificate := by
  exact ⟨block510_left_V_pos, block510_right_V_pos⟩

end Block510
end M1817475
end Erdos1038Lean
