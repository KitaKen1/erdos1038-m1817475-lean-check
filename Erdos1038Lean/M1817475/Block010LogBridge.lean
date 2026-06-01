import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block010

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block010

open Set

def block010W1 : Rat := ((9575327037577903 : Rat) / 1000000000000000)
def block010W2 : Rat := (0 : Rat)
def block010W3 : Rat := (0 : Rat)
def block010W4 : Rat := ((2526066277374633 : Rat) / 10000000000000000)
def block010S1 : Rat := ((18174751 : Rat) / 10000000)
def block010S2 : Rat := ((511587 : Rat) / 200000)
def block010S3 : Rat := ((107000619 : Rat) / 40000000)
def block010S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block010V (y : ℝ) : ℝ :=
  ratPotential block010W1 block010W2 block010W3 block010W4 block010S1 block010S2 block010S3 block010S4 y

def block010LeftParamsCertificate : Bool :=
  allBoxesSameParams block010LeftBoxes block010W1 block010W2 block010W3 block010W4 block010S1 block010S2 block010S3 block010S4

theorem block010LeftParamsCertificate_eq_true :
    block010LeftParamsCertificate = true := by
  native_decide

theorem block010_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block010LeftL : ℝ) (block010LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block010S1 : ℝ))
    (hy2ne : y ≠ (block010S2 : ℝ))
    (hy3ne : y ≠ (block010S3 : ℝ))
    (hy4ne : y ≠ (block010S4 : ℝ)) :
    0 < block010V y := by
  have hcert := block010LeftCertificate_eq_true
  unfold block010LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block010LeftBoxes) (lo := block010LeftL) (hi := block010LeftR)
    (w1 := block010W1) (w2 := block010W2) (w3 := block010W3) (w4 := block010W4)
    (s1 := block010S1) (s2 := block010S2) (s3 := block010S3) (s4 := block010S4)
    hboxes hcover block010LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block010RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block010RightChunk000 block010W1 block010W2 block010W3 block010W4 block010S1 block010S2 block010S3 block010S4

theorem block010RightChunk000ParamsCertificate_eq_true :
    block010RightChunk000ParamsCertificate = true := by
  native_decide

theorem block010_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block010RightChunk000L : ℝ) (block010RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block010S1 : ℝ))
    (hy2ne : y ≠ (block010S2 : ℝ))
    (hy3ne : y ≠ (block010S3 : ℝ))
    (hy4ne : y ≠ (block010S4 : ℝ)) :
    0 < block010V y := by
  have hcert := block010RightChunk000Certificate_eq_true
  unfold block010RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block010RightChunk000) (lo := block010RightChunk000L) (hi := block010RightChunk000R)
    (w1 := block010W1) (w2 := block010W2) (w3 := block010W3) (w4 := block010W4)
    (s1 := block010S1) (s2 := block010S2) (s3 := block010S3) (s4 := block010S4)
    hboxes hcover block010RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block010_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block010RightL : ℝ) (block010RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block010S1 : ℝ))
    (hy2ne : y ≠ (block010S2 : ℝ))
    (hy3ne : y ≠ (block010S3 : ℝ))
    (hy4ne : y ≠ (block010S4 : ℝ)) :
    0 < block010V y := by
  have hL : (block010RightChunk000L : ℝ) = (block010RightL : ℝ) := by
    norm_num [block010RightChunk000L, block010RightL]
  have hR : (block010RightChunk000R : ℝ) = (block010RightR : ℝ) := by
    norm_num [block010RightChunk000R, block010RightR]
  have hyc : y ∈ Icc (block010RightChunk000L : ℝ) (block010RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block010_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block010_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block010LeftL : ℝ) (block010LeftR : ℝ) →
    y ≠ 0 → y ≠ (block010S1 : ℝ) → y ≠ (block010S2 : ℝ) →
    y ≠ (block010S3 : ℝ) → y ≠ (block010S4 : ℝ) → 0 < block010V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block010RightL : ℝ) (block010RightR : ℝ) →
    y ≠ 0 → y ≠ (block010S1 : ℝ) → y ≠ (block010S2 : ℝ) →
    y ≠ (block010S3 : ℝ) → y ≠ (block010S4 : ℝ) → 0 < block010V y)

theorem block010_reallog_certificate_proof :
    block010_reallog_certificate := by
  exact ⟨block010_left_V_pos, block010_right_V_pos⟩

end Block010
end M1817475
end Erdos1038Lean
