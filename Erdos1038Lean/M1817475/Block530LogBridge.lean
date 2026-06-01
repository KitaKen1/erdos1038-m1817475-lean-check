import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block530

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block530

open Set

def block530W1 : Rat := ((20391178814124747 : Rat) / 50000000000000000)
def block530W2 : Rat := (0 : Rat)
def block530W3 : Rat := ((5652410146867843 : Rat) / 12500000000000000)
def block530W4 : Rat := (0 : Rat)
def block530S1 : Rat := ((18174751 : Rat) / 10000000)
def block530S2 : Rat := ((511587 : Rat) / 200000)
def block530S3 : Rat := ((129772530446428571603 : Rat) / 50000000000000000000)
def block530S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block530V (y : ℝ) : ℝ :=
  ratPotential block530W1 block530W2 block530W3 block530W4 block530S1 block530S2 block530S3 block530S4 y

def block530LeftParamsCertificate : Bool :=
  allBoxesSameParams block530LeftBoxes block530W1 block530W2 block530W3 block530W4 block530S1 block530S2 block530S3 block530S4

theorem block530LeftParamsCertificate_eq_true :
    block530LeftParamsCertificate = true := by
  native_decide

theorem block530_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block530LeftL : ℝ) (block530LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block530S1 : ℝ))
    (hy2ne : y ≠ (block530S2 : ℝ))
    (hy3ne : y ≠ (block530S3 : ℝ))
    (hy4ne : y ≠ (block530S4 : ℝ)) :
    0 < block530V y := by
  have hcert := block530LeftCertificate_eq_true
  unfold block530LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block530LeftBoxes) (lo := block530LeftL) (hi := block530LeftR)
    (w1 := block530W1) (w2 := block530W2) (w3 := block530W3) (w4 := block530W4)
    (s1 := block530S1) (s2 := block530S2) (s3 := block530S3) (s4 := block530S4)
    hboxes hcover block530LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block530RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block530RightChunk000 block530W1 block530W2 block530W3 block530W4 block530S1 block530S2 block530S3 block530S4

theorem block530RightChunk000ParamsCertificate_eq_true :
    block530RightChunk000ParamsCertificate = true := by
  native_decide

theorem block530_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block530RightChunk000L : ℝ) (block530RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block530S1 : ℝ))
    (hy2ne : y ≠ (block530S2 : ℝ))
    (hy3ne : y ≠ (block530S3 : ℝ))
    (hy4ne : y ≠ (block530S4 : ℝ)) :
    0 < block530V y := by
  have hcert := block530RightChunk000Certificate_eq_true
  unfold block530RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block530RightChunk000) (lo := block530RightChunk000L) (hi := block530RightChunk000R)
    (w1 := block530W1) (w2 := block530W2) (w3 := block530W3) (w4 := block530W4)
    (s1 := block530S1) (s2 := block530S2) (s3 := block530S3) (s4 := block530S4)
    hboxes hcover block530RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block530_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block530RightL : ℝ) (block530RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block530S1 : ℝ))
    (hy2ne : y ≠ (block530S2 : ℝ))
    (hy3ne : y ≠ (block530S3 : ℝ))
    (hy4ne : y ≠ (block530S4 : ℝ)) :
    0 < block530V y := by
  have hL : (block530RightChunk000L : ℝ) = (block530RightL : ℝ) := by
    norm_num [block530RightChunk000L, block530RightL]
  have hR : (block530RightChunk000R : ℝ) = (block530RightR : ℝ) := by
    norm_num [block530RightChunk000R, block530RightR]
  have hyc : y ∈ Icc (block530RightChunk000L : ℝ) (block530RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block530_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block530_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block530LeftL : ℝ) (block530LeftR : ℝ) →
    y ≠ 0 → y ≠ (block530S1 : ℝ) → y ≠ (block530S2 : ℝ) →
    y ≠ (block530S3 : ℝ) → y ≠ (block530S4 : ℝ) → 0 < block530V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block530RightL : ℝ) (block530RightR : ℝ) →
    y ≠ 0 → y ≠ (block530S1 : ℝ) → y ≠ (block530S2 : ℝ) →
    y ≠ (block530S3 : ℝ) → y ≠ (block530S4 : ℝ) → 0 < block530V y)

theorem block530_reallog_certificate_proof :
    block530_reallog_certificate := by
  exact ⟨block530_left_V_pos, block530_right_V_pos⟩

end Block530
end M1817475
end Erdos1038Lean
