import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block026

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block026

open Set

def block026W1 : Rat := ((2319051519092837 : Rat) / 1000000000000000)
def block026W2 : Rat := (0 : Rat)
def block026W3 : Rat := (0 : Rat)
def block026W4 : Rat := ((2860370660938681 : Rat) / 10000000000000000)
def block026S1 : Rat := ((18174751 : Rat) / 10000000)
def block026S2 : Rat := ((511587 : Rat) / 200000)
def block026S3 : Rat := ((107000619 : Rat) / 40000000)
def block026S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block026V (y : ℝ) : ℝ :=
  ratPotential block026W1 block026W2 block026W3 block026W4 block026S1 block026S2 block026S3 block026S4 y

def block026LeftParamsCertificate : Bool :=
  allBoxesSameParams block026LeftBoxes block026W1 block026W2 block026W3 block026W4 block026S1 block026S2 block026S3 block026S4

theorem block026LeftParamsCertificate_eq_true :
    block026LeftParamsCertificate = true := by
  native_decide

theorem block026_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block026LeftL : ℝ) (block026LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block026S1 : ℝ))
    (hy2ne : y ≠ (block026S2 : ℝ))
    (hy3ne : y ≠ (block026S3 : ℝ))
    (hy4ne : y ≠ (block026S4 : ℝ)) :
    0 < block026V y := by
  have hcert := block026LeftCertificate_eq_true
  unfold block026LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block026LeftBoxes) (lo := block026LeftL) (hi := block026LeftR)
    (w1 := block026W1) (w2 := block026W2) (w3 := block026W3) (w4 := block026W4)
    (s1 := block026S1) (s2 := block026S2) (s3 := block026S3) (s4 := block026S4)
    hboxes hcover block026LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block026RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block026RightChunk000 block026W1 block026W2 block026W3 block026W4 block026S1 block026S2 block026S3 block026S4

theorem block026RightChunk000ParamsCertificate_eq_true :
    block026RightChunk000ParamsCertificate = true := by
  native_decide

theorem block026_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block026RightChunk000L : ℝ) (block026RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block026S1 : ℝ))
    (hy2ne : y ≠ (block026S2 : ℝ))
    (hy3ne : y ≠ (block026S3 : ℝ))
    (hy4ne : y ≠ (block026S4 : ℝ)) :
    0 < block026V y := by
  have hcert := block026RightChunk000Certificate_eq_true
  unfold block026RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block026RightChunk000) (lo := block026RightChunk000L) (hi := block026RightChunk000R)
    (w1 := block026W1) (w2 := block026W2) (w3 := block026W3) (w4 := block026W4)
    (s1 := block026S1) (s2 := block026S2) (s3 := block026S3) (s4 := block026S4)
    hboxes hcover block026RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block026_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block026RightL : ℝ) (block026RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block026S1 : ℝ))
    (hy2ne : y ≠ (block026S2 : ℝ))
    (hy3ne : y ≠ (block026S3 : ℝ))
    (hy4ne : y ≠ (block026S4 : ℝ)) :
    0 < block026V y := by
  have hL : (block026RightChunk000L : ℝ) = (block026RightL : ℝ) := by
    norm_num [block026RightChunk000L, block026RightL]
  have hR : (block026RightChunk000R : ℝ) = (block026RightR : ℝ) := by
    norm_num [block026RightChunk000R, block026RightR]
  have hyc : y ∈ Icc (block026RightChunk000L : ℝ) (block026RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block026_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block026_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block026LeftL : ℝ) (block026LeftR : ℝ) →
    y ≠ 0 → y ≠ (block026S1 : ℝ) → y ≠ (block026S2 : ℝ) →
    y ≠ (block026S3 : ℝ) → y ≠ (block026S4 : ℝ) → 0 < block026V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block026RightL : ℝ) (block026RightR : ℝ) →
    y ≠ 0 → y ≠ (block026S1 : ℝ) → y ≠ (block026S2 : ℝ) →
    y ≠ (block026S3 : ℝ) → y ≠ (block026S4 : ℝ) → 0 < block026V y)

theorem block026_reallog_certificate_proof :
    block026_reallog_certificate := by
  exact ⟨block026_left_V_pos, block026_right_V_pos⟩

end Block026
end M1817475
end Erdos1038Lean
