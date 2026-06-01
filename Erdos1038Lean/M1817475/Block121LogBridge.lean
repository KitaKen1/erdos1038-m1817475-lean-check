import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block121

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block121

open Set

def block121W1 : Rat := ((359848596828473 : Rat) / 156250000000000)
def block121W2 : Rat := (0 : Rat)
def block121W3 : Rat := ((9519697507595867 : Rat) / 100000000000000000)
def block121W4 : Rat := ((195163278769229 : Rat) / 1250000000000000)
def block121S1 : Rat := ((18174751 : Rat) / 10000000)
def block121S2 : Rat := ((511587 : Rat) / 200000)
def block121S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block121S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block121V (y : ℝ) : ℝ :=
  ratPotential block121W1 block121W2 block121W3 block121W4 block121S1 block121S2 block121S3 block121S4 y

def block121LeftParamsCertificate : Bool :=
  allBoxesSameParams block121LeftBoxes block121W1 block121W2 block121W3 block121W4 block121S1 block121S2 block121S3 block121S4

theorem block121LeftParamsCertificate_eq_true :
    block121LeftParamsCertificate = true := by
  native_decide

theorem block121_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block121LeftL : ℝ) (block121LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block121S1 : ℝ))
    (hy2ne : y ≠ (block121S2 : ℝ))
    (hy3ne : y ≠ (block121S3 : ℝ))
    (hy4ne : y ≠ (block121S4 : ℝ)) :
    0 < block121V y := by
  have hcert := block121LeftCertificate_eq_true
  unfold block121LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block121LeftBoxes) (lo := block121LeftL) (hi := block121LeftR)
    (w1 := block121W1) (w2 := block121W2) (w3 := block121W3) (w4 := block121W4)
    (s1 := block121S1) (s2 := block121S2) (s3 := block121S3) (s4 := block121S4)
    hboxes hcover block121LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block121RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block121RightChunk000 block121W1 block121W2 block121W3 block121W4 block121S1 block121S2 block121S3 block121S4

theorem block121RightChunk000ParamsCertificate_eq_true :
    block121RightChunk000ParamsCertificate = true := by
  native_decide

theorem block121_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block121RightChunk000L : ℝ) (block121RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block121S1 : ℝ))
    (hy2ne : y ≠ (block121S2 : ℝ))
    (hy3ne : y ≠ (block121S3 : ℝ))
    (hy4ne : y ≠ (block121S4 : ℝ)) :
    0 < block121V y := by
  have hcert := block121RightChunk000Certificate_eq_true
  unfold block121RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block121RightChunk000) (lo := block121RightChunk000L) (hi := block121RightChunk000R)
    (w1 := block121W1) (w2 := block121W2) (w3 := block121W3) (w4 := block121W4)
    (s1 := block121S1) (s2 := block121S2) (s3 := block121S3) (s4 := block121S4)
    hboxes hcover block121RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block121_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block121RightL : ℝ) (block121RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block121S1 : ℝ))
    (hy2ne : y ≠ (block121S2 : ℝ))
    (hy3ne : y ≠ (block121S3 : ℝ))
    (hy4ne : y ≠ (block121S4 : ℝ)) :
    0 < block121V y := by
  have hL : (block121RightChunk000L : ℝ) = (block121RightL : ℝ) := by
    norm_num [block121RightChunk000L, block121RightL]
  have hR : (block121RightChunk000R : ℝ) = (block121RightR : ℝ) := by
    norm_num [block121RightChunk000R, block121RightR]
  have hyc : y ∈ Icc (block121RightChunk000L : ℝ) (block121RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block121_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block121_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block121LeftL : ℝ) (block121LeftR : ℝ) →
    y ≠ 0 → y ≠ (block121S1 : ℝ) → y ≠ (block121S2 : ℝ) →
    y ≠ (block121S3 : ℝ) → y ≠ (block121S4 : ℝ) → 0 < block121V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block121RightL : ℝ) (block121RightR : ℝ) →
    y ≠ 0 → y ≠ (block121S1 : ℝ) → y ≠ (block121S2 : ℝ) →
    y ≠ (block121S3 : ℝ) → y ≠ (block121S4 : ℝ) → 0 < block121V y)

theorem block121_reallog_certificate_proof :
    block121_reallog_certificate := by
  exact ⟨block121_left_V_pos, block121_right_V_pos⟩

end Block121
end M1817475
end Erdos1038Lean
