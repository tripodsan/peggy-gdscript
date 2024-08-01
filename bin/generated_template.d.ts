/** Provides information pointing to a location within a source. */
export interface Location {
  /** Line in the parsed source (1-based). */
  readonly line: number;
  /** Column in the parsed source (1-based). */
  readonly column: number;
  /** Offset in the parsed source (0-based). */
  readonly offset: number;
}

export interface Stringable {
  readonly toString: () => string;
}

export interface GrammarSourceObject extends Stringable {
  readonly source?: undefined | string | Stringable;
  readonly offset?: undefined | ((loc: Location) => Location);
}

export type GrammarSource = string | GrammarSourceObject;

/** The `start` and `end` position's of an object within the source. */
export interface LocationRange {
  /**
   * A string or object that was supplied to the `parse()` call as the
   * `grammarSource` option.
   */
  readonly source: GrammarSource;
  /** Position at the beginning of the expression. */
  readonly start: Location;
  /** Position after the end of the expression. */
  readonly end: Location;
}

export interface LiteralExpectation {
  readonly type: "literal";
  readonly text: string;
  readonly ignoreCase: boolean;
}

export type ClassRange = [
  start: string,
  end: string,
]
export interface ClassParts extends Array<string | ClassRange> {
}
export interface ClassExpectation {
  readonly type: "class";
  readonly parts: ClassParts;
  readonly inverted: boolean;
  readonly ignoreCase: boolean;
}
export interface AnyExpectation {
  readonly type: "any";
}
export interface EndExpectation {
  readonly type: "end";
}
export interface OtherExpectation {
  readonly type: "other";
  readonly description: string;
}
export type Expectation =
  | AnyExpectation
  | ClassExpectation
  | EndExpectation
  | LiteralExpectation
  | OtherExpectation;

export interface SourceText {
  /**
   * Identifier of an input that was used as a grammarSource in parse().
   */
  readonly source: GrammarSource;
  /** Source text of the input. */
  readonly text: string;
}

export declare class SyntaxError extends Error {
  /**
   * Constructs the human-readable message from the machine representation.
   *
   * @param expected Array of expected items, generated by the parser
   * @param found Any text that will appear as found in the input instead of
   *   expected
   */
  static buildMessage(expected: Expectation[], found?: string | null | undefined): string;
  readonly message: string;
  readonly expected: Expectation[];
  readonly found: string | null | undefined;
  readonly location: LocationRange;
  readonly name: string;
  constructor(
    message: string,
    expected: Expectation[],
    found: string | null,
    location: LocationRange,
  );
  format(sources: SourceText[]): string;
}

export interface ParserTracer {
  trace: (event: ParserTracerEvent) => void;
}

export type ParserTracerEvent
  = { readonly type: "rule.enter"; readonly rule: string; readonly location: LocationRange }
  | { readonly type: "rule.fail"; readonly rule: string; readonly location: LocationRange }
  | {
      readonly type: "rule.match";
      readonly rule: string;
      readonly location: LocationRange
      /** Return value from the rule. */
      readonly result: unknown;
    };

export type StartRules = $$$StartRules$$$;
export interface ParseOptions<T extends StartRules = $$$DefaultStartRule$$$> {
  /**
   * String or object that will be attached to the each `LocationRange` object
   * created by the parser. For example, this can be path to the parsed file
   * or even the File object.
   */
  readonly grammarSource?: GrammarSource;
  readonly startRule?: T;
  readonly tracer?: ParserTracer;

  // Internal use only:
  readonly peg$library?: boolean;
  // Internal use only:
  peg$currPos?: number;
  // Internal use only:
  peg$silentFails?: number;
  // Internal use only:
  peg$maxFailExpected?: Expectation[];
  // Extra application-specific properties
  [key: string]: unknown;
}

export declare const parse: typeof ParseFunction;
export declare const SyntaxError: typeof _PeggySyntaxError;

// Overload of ParseFunction for each allowedStartRule
