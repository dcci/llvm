; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+sse2 | FileCheck %s --check-prefix=CHECK --check-prefix=SSE
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx  | FileCheck %s --check-prefix=CHECK --check-prefix=AVX

; It's the extra tests coverage for recip as discussed on D26855.

define float @f32_no_step_2(float %x) #3 {
; SSE-LABEL: f32_no_step_2:
; SSE:       # BB#0:
; SSE-NEXT:    rcpss %xmm0, %xmm0
; SSE-NEXT:    mulss {{.*}}(%rip), %xmm0
; SSE-NEXT:    retq
;
; AVX-LABEL: f32_no_step_2:
; AVX:       # BB#0:
; AVX-NEXT:    vrcpss %xmm0, %xmm0, %xmm0
; AVX-NEXT:    vmulss {{.*}}(%rip), %xmm0, %xmm0
; AVX-NEXT:    retq
  %div = fdiv fast float 1234.0, %x
  ret float %div
}

define float @f32_one_step_2(float %x) #1 {
; SSE-LABEL: f32_one_step_2:
; SSE:       # BB#0:
; SSE-NEXT:    rcpss %xmm0, %xmm2
; SSE-NEXT:    mulss %xmm2, %xmm0
; SSE-NEXT:    movss {{.*#+}} xmm1 = mem[0],zero,zero,zero
; SSE-NEXT:    subss %xmm0, %xmm1
; SSE-NEXT:    mulss %xmm2, %xmm1
; SSE-NEXT:    addss %xmm2, %xmm1
; SSE-NEXT:    mulss {{.*}}(%rip), %xmm1
; SSE-NEXT:    movaps %xmm1, %xmm0
; SSE-NEXT:    retq
;
; AVX-LABEL: f32_one_step_2:
; AVX:       # BB#0:
; AVX-NEXT:    vrcpss %xmm0, %xmm0, %xmm1
; AVX-NEXT:    vmulss %xmm1, %xmm0, %xmm0
; AVX-NEXT:    vmovss {{.*#+}} xmm2 = mem[0],zero,zero,zero
; AVX-NEXT:    vsubss %xmm0, %xmm2, %xmm0
; AVX-NEXT:    vmulss %xmm0, %xmm1, %xmm0
; AVX-NEXT:    vaddss %xmm0, %xmm1, %xmm0
; AVX-NEXT:    vmulss {{.*}}(%rip), %xmm0, %xmm0
; AVX-NEXT:    retq
  %div = fdiv fast float 3456.0, %x
  ret float %div
}

define float @f32_two_step_2(float %x) #2 {
; SSE-LABEL: f32_two_step_2:
; SSE:       # BB#0:
; SSE-NEXT:    rcpss %xmm0, %xmm2
; SSE-NEXT:    movaps %xmm0, %xmm3
; SSE-NEXT:    mulss %xmm2, %xmm3
; SSE-NEXT:    movss {{.*#+}} xmm1 = mem[0],zero,zero,zero
; SSE-NEXT:    movaps %xmm1, %xmm4
; SSE-NEXT:    subss %xmm3, %xmm4
; SSE-NEXT:    mulss %xmm2, %xmm4
; SSE-NEXT:    addss %xmm2, %xmm4
; SSE-NEXT:    mulss %xmm4, %xmm0
; SSE-NEXT:    subss %xmm0, %xmm1
; SSE-NEXT:    mulss %xmm4, %xmm1
; SSE-NEXT:    addss %xmm4, %xmm1
; SSE-NEXT:    mulss {{.*}}(%rip), %xmm1
; SSE-NEXT:    movaps %xmm1, %xmm0
; SSE-NEXT:    retq
;
; AVX-LABEL: f32_two_step_2:
; AVX:       # BB#0:
; AVX-NEXT:    vrcpss %xmm0, %xmm0, %xmm1
; AVX-NEXT:    vmulss %xmm1, %xmm0, %xmm2
; AVX-NEXT:    vmovss {{.*#+}} xmm3 = mem[0],zero,zero,zero
; AVX-NEXT:    vsubss %xmm2, %xmm3, %xmm2
; AVX-NEXT:    vmulss %xmm2, %xmm1, %xmm2
; AVX-NEXT:    vaddss %xmm2, %xmm1, %xmm1
; AVX-NEXT:    vmulss %xmm1, %xmm0, %xmm0
; AVX-NEXT:    vsubss %xmm0, %xmm3, %xmm0
; AVX-NEXT:    vmulss %xmm0, %xmm1, %xmm0
; AVX-NEXT:    vaddss %xmm0, %xmm1, %xmm0
; AVX-NEXT:    vmulss {{.*}}(%rip), %xmm0, %xmm0
; AVX-NEXT:    retq
  %div = fdiv fast float 6789.0, %x
  ret float %div
}

define <4 x float> @v4f32_one_step2(<4 x float> %x) #1 {
; SSE-LABEL: v4f32_one_step2:
; SSE:       # BB#0:
; SSE-NEXT:    rcpps %xmm0, %xmm2
; SSE-NEXT:    mulps %xmm2, %xmm0
; SSE-NEXT:    movaps {{.*#+}} xmm1 = [1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00]
; SSE-NEXT:    subps %xmm0, %xmm1
; SSE-NEXT:    mulps %xmm2, %xmm1
; SSE-NEXT:    addps %xmm2, %xmm1
; SSE-NEXT:    mulps {{.*}}(%rip), %xmm1
; SSE-NEXT:    movaps %xmm1, %xmm0
; SSE-NEXT:    retq
;
; AVX-LABEL: v4f32_one_step2:
; AVX:       # BB#0:
; AVX-NEXT:    vrcpps %xmm0, %xmm1
; AVX-NEXT:    vmulps %xmm1, %xmm0, %xmm0
; AVX-NEXT:    vmovaps {{.*#+}} xmm2 = [1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00]
; AVX-NEXT:    vsubps %xmm0, %xmm2, %xmm0
; AVX-NEXT:    vmulps %xmm0, %xmm1, %xmm0
; AVX-NEXT:    vaddps %xmm0, %xmm1, %xmm0
; AVX-NEXT:    vmulps {{.*}}(%rip), %xmm0, %xmm0
; AVX-NEXT:    retq
  %div = fdiv fast <4 x float> <float 1.0, float 2.0, float 3.0, float 4.0>, %x
  ret <4 x float> %div
}

define <4 x float> @v4f32_two_step2(<4 x float> %x) #2 {
; SSE-LABEL: v4f32_two_step2:
; SSE:       # BB#0:
; SSE-NEXT:    rcpps %xmm0, %xmm2
; SSE-NEXT:    movaps %xmm0, %xmm3
; SSE-NEXT:    mulps %xmm2, %xmm3
; SSE-NEXT:    movaps {{.*#+}} xmm1 = [1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00]
; SSE-NEXT:    movaps %xmm1, %xmm4
; SSE-NEXT:    subps %xmm3, %xmm4
; SSE-NEXT:    mulps %xmm2, %xmm4
; SSE-NEXT:    addps %xmm2, %xmm4
; SSE-NEXT:    mulps %xmm4, %xmm0
; SSE-NEXT:    subps %xmm0, %xmm1
; SSE-NEXT:    mulps %xmm4, %xmm1
; SSE-NEXT:    addps %xmm4, %xmm1
; SSE-NEXT:    mulps {{.*}}(%rip), %xmm1
; SSE-NEXT:    movaps %xmm1, %xmm0
; SSE-NEXT:    retq
;
; AVX-LABEL: v4f32_two_step2:
; AVX:       # BB#0:
; AVX-NEXT:    vrcpps %xmm0, %xmm1
; AVX-NEXT:    vmulps %xmm1, %xmm0, %xmm2
; AVX-NEXT:    vmovaps {{.*#+}} xmm3 = [1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00]
; AVX-NEXT:    vsubps %xmm2, %xmm3, %xmm2
; AVX-NEXT:    vmulps %xmm2, %xmm1, %xmm2
; AVX-NEXT:    vaddps %xmm2, %xmm1, %xmm1
; AVX-NEXT:    vmulps %xmm1, %xmm0, %xmm0
; AVX-NEXT:    vsubps %xmm0, %xmm3, %xmm0
; AVX-NEXT:    vmulps %xmm0, %xmm1, %xmm0
; AVX-NEXT:    vaddps %xmm0, %xmm1, %xmm0
; AVX-NEXT:    vmulps {{.*}}(%rip), %xmm0, %xmm0
; AVX-NEXT:    retq
  %div = fdiv fast <4 x float> <float 1.0, float 2.0, float 3.0, float 4.0>, %x
  ret <4 x float> %div
}

define <8 x float> @v8f32_one_step2(<8 x float> %x) #1 {
; SSE-LABEL: v8f32_one_step2:
; SSE:       # BB#0:
; SSE-NEXT:    rcpps %xmm1, %xmm4
; SSE-NEXT:    mulps %xmm4, %xmm1
; SSE-NEXT:    movaps {{.*#+}} xmm2 = [1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00]
; SSE-NEXT:    movaps %xmm2, %xmm3
; SSE-NEXT:    subps %xmm1, %xmm3
; SSE-NEXT:    mulps %xmm4, %xmm3
; SSE-NEXT:    addps %xmm4, %xmm3
; SSE-NEXT:    rcpps %xmm0, %xmm1
; SSE-NEXT:    mulps %xmm1, %xmm0
; SSE-NEXT:    subps %xmm0, %xmm2
; SSE-NEXT:    mulps %xmm1, %xmm2
; SSE-NEXT:    addps %xmm1, %xmm2
; SSE-NEXT:    mulps {{.*}}(%rip), %xmm2
; SSE-NEXT:    mulps {{.*}}(%rip), %xmm3
; SSE-NEXT:    movaps %xmm2, %xmm0
; SSE-NEXT:    movaps %xmm3, %xmm1
; SSE-NEXT:    retq
;
; AVX-LABEL: v8f32_one_step2:
; AVX:       # BB#0:
; AVX-NEXT:    vrcpps %ymm0, %ymm1
; AVX-NEXT:    vmulps %ymm1, %ymm0, %ymm0
; AVX-NEXT:    vmovaps {{.*#+}} ymm2 = [1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00]
; AVX-NEXT:    vsubps %ymm0, %ymm2, %ymm0
; AVX-NEXT:    vmulps %ymm0, %ymm1, %ymm0
; AVX-NEXT:    vaddps %ymm0, %ymm1, %ymm0
; AVX-NEXT:    vmulps {{.*}}(%rip), %ymm0, %ymm0
; AVX-NEXT:    retq
  %div = fdiv fast <8 x float> <float 1.0, float 2.0, float 3.0, float 4.0, float 5.0, float 6.0, float 7.0, float 8.0>, %x
  ret <8 x float> %div
}

define <8 x float> @v8f32_two_step2(<8 x float> %x) #2 {
; SSE-LABEL: v8f32_two_step2:
; SSE:       # BB#0:
; SSE-NEXT:    movaps %xmm0, %xmm2
; SSE-NEXT:    rcpps %xmm1, %xmm3
; SSE-NEXT:    movaps %xmm1, %xmm4
; SSE-NEXT:    mulps %xmm3, %xmm4
; SSE-NEXT:    movaps {{.*#+}} xmm0 = [1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00]
; SSE-NEXT:    movaps %xmm0, %xmm5
; SSE-NEXT:    subps %xmm4, %xmm5
; SSE-NEXT:    mulps %xmm3, %xmm5
; SSE-NEXT:    addps %xmm3, %xmm5
; SSE-NEXT:    mulps %xmm5, %xmm1
; SSE-NEXT:    movaps %xmm0, %xmm3
; SSE-NEXT:    subps %xmm1, %xmm3
; SSE-NEXT:    mulps %xmm5, %xmm3
; SSE-NEXT:    addps %xmm5, %xmm3
; SSE-NEXT:    rcpps %xmm2, %xmm1
; SSE-NEXT:    movaps %xmm2, %xmm4
; SSE-NEXT:    mulps %xmm1, %xmm4
; SSE-NEXT:    movaps %xmm0, %xmm5
; SSE-NEXT:    subps %xmm4, %xmm5
; SSE-NEXT:    mulps %xmm1, %xmm5
; SSE-NEXT:    addps %xmm1, %xmm5
; SSE-NEXT:    mulps %xmm5, %xmm2
; SSE-NEXT:    subps %xmm2, %xmm0
; SSE-NEXT:    mulps %xmm5, %xmm0
; SSE-NEXT:    addps %xmm5, %xmm0
; SSE-NEXT:    mulps {{.*}}(%rip), %xmm0
; SSE-NEXT:    mulps {{.*}}(%rip), %xmm3
; SSE-NEXT:    movaps %xmm3, %xmm1
; SSE-NEXT:    retq
;
; AVX-LABEL: v8f32_two_step2:
; AVX:       # BB#0:
; AVX-NEXT:    vrcpps %ymm0, %ymm1
; AVX-NEXT:    vmulps %ymm1, %ymm0, %ymm2
; AVX-NEXT:    vmovaps {{.*#+}} ymm3 = [1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00,1.000000e+00]
; AVX-NEXT:    vsubps %ymm2, %ymm3, %ymm2
; AVX-NEXT:    vmulps %ymm2, %ymm1, %ymm2
; AVX-NEXT:    vaddps %ymm2, %ymm1, %ymm1
; AVX-NEXT:    vmulps %ymm1, %ymm0, %ymm0
; AVX-NEXT:    vsubps %ymm0, %ymm3, %ymm0
; AVX-NEXT:    vmulps %ymm0, %ymm1, %ymm0
; AVX-NEXT:    vaddps %ymm0, %ymm1, %ymm0
; AVX-NEXT:    vmulps {{.*}}(%rip), %ymm0, %ymm0
; AVX-NEXT:    retq
  %div = fdiv fast <8 x float> <float 1.0, float 2.0, float 3.0, float 4.0, float 5.0, float 6.0, float 7.0, float 8.0>, %x
  ret <8 x float> %div
}

define <8 x float> @v8f32_no_step(<8 x float> %x) #3 {
; SSE-LABEL: v8f32_no_step:
; SSE:       # BB#0:
; SSE-NEXT:    rcpps %xmm0, %xmm0
; SSE-NEXT:    rcpps %xmm1, %xmm1
; SSE-NEXT:    retq
;
; AVX-LABEL: v8f32_no_step:
; AVX:       # BB#0:
; AVX-NEXT:    vrcpps %ymm0, %ymm0
; AVX-NEXT:    retq
  %div = fdiv fast <8 x float> <float 1.0, float 1.0, float 1.0, float 1.0, float 1.0, float 1.0, float 1.0, float 1.0>, %x
  ret <8 x float> %div
}

define <8 x float> @v8f32_no_step2(<8 x float> %x) #3 {
; SSE-LABEL: v8f32_no_step2:
; SSE:       # BB#0:
; SSE-NEXT:    rcpps %xmm1, %xmm1
; SSE-NEXT:    rcpps %xmm0, %xmm0
; SSE-NEXT:    mulps {{.*}}(%rip), %xmm0
; SSE-NEXT:    mulps {{.*}}(%rip), %xmm1
; SSE-NEXT:    retq
;
; AVX-LABEL: v8f32_no_step2:
; AVX:       # BB#0:
; AVX-NEXT:    vrcpps %ymm0, %ymm0
; AVX-NEXT:    vmulps {{.*}}(%rip), %ymm0, %ymm0
; AVX-NEXT:    retq
  %div = fdiv fast <8 x float> <float 1.0, float 2.0, float 3.0, float 4.0, float 5.0, float 6.0, float 7.0, float 8.0>, %x
  ret <8 x float> %div
}

attributes #0 = { "unsafe-fp-math"="true" "reciprocal-estimates"="!divf,!vec-divf" }
attributes #1 = { "unsafe-fp-math"="true" "reciprocal-estimates"="divf,vec-divf" }
attributes #2 = { "unsafe-fp-math"="true" "reciprocal-estimates"="divf:2,vec-divf:2" }
attributes #3 = { "unsafe-fp-math"="true" "reciprocal-estimates"="divf:0,vec-divf:0" }

