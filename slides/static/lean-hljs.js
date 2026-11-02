// highlight.js grammar for Lean statements shown as plain code: the slides build on
// Verso's toolchain, not core's, so the theorems can't be elaborated here.
RevealHighlight().hljs.registerLanguage('lean4', hljs => ({
  keywords: {
    keyword: 'theorem def structure where fun by namespace end let in if then else',
    type: 'Nat Int Array ByteArray List Prop Pcm Format Clip Settings PackedPcm',
    literal: 'ok true false'
  },
  contains: [
    hljs.COMMENT('--', '$'),
    hljs.C_NUMBER_MODE
  ]
}));
