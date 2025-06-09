import {
  ASCII_MAP,
  BASE64_BIN,
  BASE64_CHAR,
  BIN_TO_ASCII,
  CHARS_SUBSCRIPT,
  CHARS_SUPERSCRIPT,
  LETTER_SUBSCRIPT,
  LETTER_SUPERSCRIPT,
  NUMBER_SUBSCRIPT,
  NUMBER_SUPERSCRIPT,
} from "./constants";
import { AsciiBinArray } from "./types/ascii-bin-array.type";
import { AsciiChar } from "./types/ascii-char.type";
import { logger } from "./classes";



/**
 * Modulo operation
 * In JS % is not the modulo operator. It's the remainder operator.
 * In JS: -1%5=-1
 * Hence, to get the expected outcome we must use this
 * @param dividend
 * @param divisor
 * @returns 
 */
export function modulo(dividend: number, divisor: number): number {
  const m = ((dividend % divisor) + divisor) % divisor;
  return m;
}



/**
 * Get modulo
 * Positive and negative
 * @param dividend
 * @param divisor
 * @returns moduli
 */
export function modulo2(dividend: number, divisor: number): [number, number] {
  const m = modulo(dividend, divisor);
  return [m - divisor, m];
}



/**
 * Ensure index is a positive number (modulo)
 * @param index 
 */
export function ensurePositive(index: number, divisor: number): number {
  return modulo(index < 0 ? index + divisor : index, divisor);
}



/**
 * Ensure positive return of the modulo operation
 * @param dividend 
 * @param divisor 
 */
export function moduloPositive(dividend: number, divisor: number): number {
  return ensurePositive(modulo(dividend, divisor), divisor);
}



/**
 * Simplified Euclidean algorithm
 * @param a 
 * @param b 
 * @returns 
 */
export function gcd(a: number, b: number): number {
  if (b === 0) {
    return a;
  } else {
    return gcd(b, a % b);
  }
}



/**
 * Split string to array
 * @param str Array | string 
 * @returns Array
 */
export function stringToArray(str: Array<string> | string): string[] {

  if (Array.isArray(str)) {
    return str;
  }

  return Array.from(
    str.split('')
  );
}



/**
 * String to map to create a map for alphabet
 * @param str 
 * @returns 
 */
export function stringToMap(str: Array<string> | string): Map<string, number> {
  const arr = stringToArray(str);
  const m = new Map(arr.map((value: string, index: number) => [value, index]));
  return m;
}



/**
 * Convert symbol to subscript (for logging)
 * @param char: string | number 
 */
export function sub(char: string | number): string {
  const strChar = String(char);
  const subMap = new Map([...LETTER_SUBSCRIPT, ...NUMBER_SUBSCRIPT, ...CHARS_SUBSCRIPT]);
  return replaceCharacters(strChar, subMap);
}



/**
 * Convert symbol to superscript (for logging)
 * @param char: string | number
 */
export function sup(char: string | number): string {
  const strChar = String(char);
  const supMap = new Map([...LETTER_SUPERSCRIPT, ...NUMBER_SUPERSCRIPT, ...CHARS_SUPERSCRIPT]);
  return replaceCharacters(strChar, supMap);
}



/**
 * superscript / subscript replacement
 * @param char 
 * @param replacementSet 
 * @returns 
 */
function replaceCharacters(char: string, replacementSet: Map<string, string>): string {
  let s: string = '';
  const parts = char.split('');
  for (let i = 0; i < parts.length; i++) {
    const symbol = replacementSet.get(parts[i]);
    s += symbol ?? parts[i];
  }
  return s;

}



/**
 * Integer division
 * @param dividend
 * @param divisor
 * @returns 
 */
export function integerDivision(dividend: number, divisor: number): number {
  return Math.floor(dividend / divisor);
}



/**
 * Check whether two number are co prime
 * @param a 
 * @param b 
 * @returns 
 */
export function areCoprime(a: number, b: number): boolean {
  return gcd(a, b) === 1;
}



/**
 * Random number
 * @param min 
 * @param max 
 * @returns 
 */
export function getRandomNumber(min: number = 0, max: number = 1): number {
  min = Math.ceil(min);
  max = Math.floor(max);
  return Math.floor(Math.random() * (max - min + 1)) + min;
}



/**
 * Random element from array
 * @param min 
 * @param max 
 * @returns 
 */
export function getRandomInArray(arr: any[]): any {
  const i = getRandomNumber(0, arr.length - 1);
  return arr[i];
}



/**
 * Convert plaintext to binary array
 * @param plaintext 
 */
export function plaintextToBinArray(plaintext: string | string[]): AsciiBinArray[] {
  const arr: AsciiBinArray[] = [];

  for (let i = 0; i < plaintext.length; i++) {
    const letter: string = plaintext[i];
    if (ASCII_MAP.has(letter)) {
      const asciiCode: AsciiChar = ASCII_MAP.get(letter);
      const asciiBin = asciiCode.bin.padStart(8, '0').split('') as AsciiBinArray;
      logger.log(`${letter} = ${asciiCode.dec}₁₀ = ${asciiCode.bin}₂`)
      arr.push(asciiBin);
    } else {
      logger.warn(`Character ${letter} is not in ASCII.`)
    }
  }

  return arr;
}



/**
 * Convert binary array to ascii text
 * @param bin array 
 */
export function binArrayToAscii(arr: string[]): string {
  let ciphertext: string = '';

  for (let i = 0; i < arr.length; i++) {
    const bin: string = arr[i];
    if (bin === '00000000') {
      continue;
    }
    if (BIN_TO_ASCII.has(bin)) {
      const asciiChar: AsciiChar = BIN_TO_ASCII.get(bin);
      logger.log(`${bin}₂ = ${asciiChar.dec}₁₀ = ${asciiChar.char}`)
      ciphertext += asciiChar.char;
    } else {
      logger.warn(`bin ${bin} is not in ASCII map.`)
    }
  }

  return ciphertext;
}



/**
 * Slice binary string in to chucks
 * 
 * str
 * size
 * pad - add padding to the last block
 */
export function slice(str: string, size: number, pad: boolean = true): string[] {

  const blocks: string[] = [];

  let i: number = 0;

  for (i = str.length; i - size > 0; i -= size) {
    const start = i - size;
    const end = i;
    const b: string = str.slice(start, end);
    if (b) {
      blocks.unshift(b);
    }
  }

  if (i) {
    let b = str.slice(0, i);
    if (pad) {
      b = b.padStart(size, '0');
    }
    // drop first block with null
    if (Number.parseInt(b, 2) !== 0) {
      blocks.unshift(b);
    }
  }

  return blocks;

}



/**
 * Slice a string into block from the start
 * 
 * str
 * size
 * pad - add adding to the last block
 */
export function sliceStart(str: string, size: number = 8, pad: boolean = false): string[] {

  const blocks: string[] = [];

  for (let i = 0; i < str.length; i += size) {
    let substr = str.slice(i, i + size);
    if (pad) {
      substr += '0'.repeat(size - substr.length);
    }
    blocks.push(substr);
  }

  return blocks;
}



/**
 * Plain text conversion to binary in string format
 * @param plaintext 
 * @returns 
 */
export function plaintextToBinString(plaintext: string) {
  return plaintextToBinArray(plaintext).flat().join('');
}



/**
 * Logarithm
 * 
 * using binary search
 * @param base
 * @param n 
 * @param depth 
 * @returns 
 */
export function log(base: number, n: number, depth: number = 20): number {
  let current: number = 64;
  let precision: number = current / 2;

  while (depth-- > 0 && base ** current !== n) {
    if (base ** current > n) {
      current -= precision;
    } else {
      current += precision;
    }
    precision /= 2;
  }
  return current;
}



/**
 * decimal to binary conversion
 * @param n - number to convert
 * @param pad number of digits to pad
 */
export function decToBin(n: number | string, pad: number = 0): string {
  if (!n && n !== 0) {
    throw new Error(`n (${n}) cannot be empty.`);
  }
  const bin: number = Number.parseInt(String(n), 10);
  if (Number.isNaN(bin)) {
    throw new Error(`${n} is not a parsable number.`);
  }
  if (pad > 0) {
    return bin.toString(2).padStart(pad, '0');
  }
  return bin.toString(2);
}



/**
 * binary to decimal conversion
 */
export function binToDec(n: number | string): number {
  return Number.parseInt(String(n), 2);
}



/**
 * Bit pair xor
 * abcdefgh
 * a^b, c^d, e^f, g^h
 * @param n binary number as string
 * @returns xor operation result as binary string
 */
export function pairXor(n: string | number): string {
  if (typeof n === 'number') {
    n = n.toString(2);
  }
  const a: string[] = [];
  const b: string[] = [];

  for (let i = 0; i < n.length; i++) {
    if (i % 2 === 0) {
      a.push(n[i]);
    } else {
      b.push(n[i]);
    }
  }
  const x: number = Number.parseInt(a.join(''), 2) ^ Number.parseInt(b.join(''), 2);
  return x.toString(2);
}



/**
 * Get filled range
 * @param length 
 * @returns 
 */
export function range(length: number): number[] {
  return [...Array(length).keys()];
}



/**
 * Generate tabs
 * @param n 
 * @returns 
 */
export function tt(n: number): string {
  // const char = '\t';
  const char = '  ';
  return `${(range(n) as any[]).fill(char).join('|')}`;
}



/**
 * Is prime number
 * @param a 
 * @returns 
 */
export function isPrime(n: number): boolean {

  const _isPrime = (num: number) => {
    for (let i = 2, s = Math.sqrt(num); i <= s; i++) {
      if (num % i === 0) return false;
    }
    return num > 1;
  };

  const result = _isPrime(n);

  return result;
}



/**
 * Get all prime factors
 * without 1
 * @param n 
 * @returns 
 */
export function primeFactors(n: number): number[] {
  const factors: number[] = [];
  let divisor: number = 2;

  while (n >= 2) {
    if (n % divisor == 0) {
      factors.push(divisor);
      n = n / divisor;
    } else {
      divisor++;
    }
  }
  return factors.sort((a, b) => a - b);
}



/**
 * Get all factors
 * Sorted, including 1
 * @param n 
 * @returns 
 */
export function getAllFactors(n: number) {

  function getPrimesMap(n: number): Map<number, number> {
    const factors: Map<number, number> = new Map();
    let divisor: number = 2;
    while (n >= 2) {
      while (n % divisor === 0) {
        factors.set(divisor, (factors.get(divisor) || 0) + 1);
        n /= divisor;
      }
      divisor++;
    }
    return factors;
  }

  const primeFactors: Map<number, number> = getPrimesMap(n);

  let factorList: number[] = [1];

  primeFactors.forEach((count, primeNumber) => {
    const newFactors: number[] = [];
    let power = 1;
    for (let i = 0; i <= count; i++) {
      factorList.forEach((factor: number) => newFactors.push(factor * power));
      power *= primeNumber;
    }
    factorList = newFactors;
  });


  return factorList.sort((a, b) => a - b);
}





/**
 * Find power of two and remainder
 * @param n
 * @param [power, mult]
 * @returns 
 */
export function getPowerOfTwoAndMultiplicator(n: number): [number, number] {

  let power: number = 0;
  let mult: number = n;

  while ((mult / 2) === Math.floor(mult / 2)) {
    power++;
    mult /= 2;
  }

  return [power, mult];
}



/**
 * Find order of an element in a group denoted by a prime number
 * for an element in ℤ*ₚ
 * @param element 
 * @param prime 
 * @returns 
 */
export function findOrderInGroup(element: number, prime: number): number | null {

  let value: number = moduloPositive(element, prime);

  // let [value] = new LargePowerModulo(element, prime, prime).calc();

  // Checking if an element is e ∈ ℤ*ₚ
  if (value === 0) {
    return null;
  }

  let order: number = 1;

  while (value !== 1) {
    value = moduloPositive(value * element, prime);
    // logger.log(new LargePowerModulo(value, element, prime).calc());
    // [value] = new LargePowerModulo(value, element, prime).calc();
    order++;
  }
  return order;
}



/**
 * shuffle an array
 * @param array 
 * @returns 
 */
export function shuffle(array: any[]) {
  const copy = [];
  let n: number = array.length
  let i: number;

  while (n) {
    i = Math.floor(Math.random() * n--);
    copy.push(array.splice(i, 1)[0]);
  }

  return copy;
}



/**
 * Binary string to base64
 */
export function binStringtoBase64(binaryString: string) {

  const binaryStringLength = binaryString.length;
  // Pad the binary string to be divisible by 6
  const padding = (6 - (binaryStringLength % 6)) % 6;
  binaryString += '0'.repeat(padding);

  const base64arr = slice(binaryString, 6, false);
  const charsList = base64arr.reduce((a: string[], n: string) => {
    if (BASE64_BIN.has(n)) {
      const char = BASE64_BIN.get(n);
      a.push(char);
    } else {
      logger.warn(`${n} is not in BASE64_BIN map.`)
    }
    return a;
  }, []);

  // An additional pad character is allocated which may be used 
  // to force the encoded output into an integer multiple of 4 characters 
  // (or equivalently when the unencoded binary text is not a multiple of 3 bytes) ; 
  // these padding characters must then be discarded when decoding but 
  // still allow the calculation of the effective length of the unencoded text, 
  // when its input binary length would not be not a multiple of 3 bytes 
  // (the last non-pad character is normally encoded so that the last 6-bit block 
  // it represents will be zero-padded on its least significant bits, 
  // at most two pad characters may occur at the end of the encoded stream).

  let base64 = charsList.join('');

  // Add padding '=' characters if needed
  const paddingChars = Math.ceil((binaryStringLength % 3) / 1.5);
  base64 += '='.repeat(paddingChars);

  return base64;

}



/**
 * Base64 for ASCII
 * chars are modulo 256
 */
export function toBase64(text: string) {

  const arr = Uint8Array.from(Array.from(text).map((letter: string) => letter.charCodeAt(0)));
  const binaryArray: string[] = arr.reduce((a: string[], n: number) => {
    a.push(n.toString(2).padStart(8, '0'));
    return a;
  }, []);

  const binaryString = binaryArray.join('');

  return binStringtoBase64(binaryString);
}



/**
 * Convert a base64 string back to the original string
 * @param base64 
 * @returns 
 */
export function fromBase64(base64: string): string {

  const binaryString = fromBase64ToBinString(base64);

  // Split into 8-bit chunks and convert to characters
  let text: string = '';

  const chunks = sliceStart(binaryString, 8);

  for (let i = 0; i < chunks.length; i++) {
    const byte = chunks[i];
    if (byte.length === 8) {
      const charCode = parseInt(byte, 2);
      text += String.fromCharCode(charCode);
    }
  }

  return text;
}



/**
 * Convert a base64 string back to binary string
 * @param base64 
 * @returns 
 */
export function fromBase64ToBinString(base64: string): string {

  // Remove padding characters and keep track of how many there were
  let paddingCount: number = 0;
  if (base64.endsWith('==')) {
    paddingCount = 2;
    base64 = base64.slice(0, base64.length - 2);
  } else if (base64.endsWith('=')) {
    paddingCount = 1;
    base64 = base64.slice(0, -1);
  }

  // Convert each Base64 character to its 6-bit binary representation
  let binaryString: string = '';
  for (const char of base64) {
    if (BASE64_CHAR.has(char)) {
      binaryString += BASE64_CHAR.get(char) || '000000';
    }
  }

  // Remove padding bits that were added during encodings
  if (paddingCount > 0) {
    binaryString = binaryString.slice(0, -paddingCount * 2);
  }

  return binaryString;
}



/**
 * Get random coprime less than n
 * 
 * @param n - to be co prime with
 * @param notLess - not less than the indicated number
 */
export function getRandomCoprime(n: number, notLess: number = 10) {

  let coprime: number;

  for (let i = notLess; i < n; i++) {
    if (areCoprime(i, n)) {
      coprime = i;
      break;
    }
  }

  return coprime;
}

/**
 * Is integer number
 * @param n 
 */
export function isInt(n: number) {
  return n % 1 === 0;
}


/**
 * Find whole divisor modulo
 * @param n1
 * @param n2
 * @param p modulo
 * @returns [whole number, multiplicator]
 */
export function divideModulo(dividend: number, divisor: number, p: number) {

  if (divisor === 0) {
    logger.log(`ERROR division by 0 in divideModulo`, 'color:red');
    return [0, 0];
  }

  // multiplicaßtor
  let m = 0;

  // hard break
  let counter = 0;

  let d = dividend / divisor;
  dividend = dividend % divisor;

  let divisionResult = Math.floor(d);


  // logger.log(` > > > > > > > > > `);
  // logger.log(`${dividend} ${divisor} ${p}\n`);

  while (!isInt(d)) {

    dividend += p;
    d = dividend / divisor;
    dividend = dividend % divisor;

    divisionResult += Math.floor(d);
    m += 1;

    // logger.log(`${m} ${dividend} ${d}`);

    if (counter > 1000) {
      logger.log(`ERROR: the number of interations is too big (calculating x3).`);
      break;
    }
  }

  return [divisionResult, m];
}

/**
 * Russian peasant multiplication
 * 
 * multiplication of two big number modulo
 * @param a big number 1
 * @param b big number 2
 * @param n modulo
 * @returns 
 */

export function multiplyMod(a: number | bigint, b: number | bigint, n: number) {
  a = BigInt(a) % BigInt(n);
  b = BigInt(b) % BigInt(n);
  let res = 0n;
  a = a < 0n ? a + BigInt(n) : a;
  b = b < 0n ? b + BigInt(n) : b;

  while (b > 0n) {
    if (b % 2n === 1n) {
      res = (res + a) % BigInt(n);
    }
    a = (a * 2n) % BigInt(n);
    b = b / 2n;
  }
  return Number(res);
}


/**
 * Get all summonds of a number
 * @param target 
 * @returns 
 */
export function getAllSummands(target: number): number[] {
  let summands: number[] = [1]; // Start with 1
  let sum = 1;

  // Double until exceeding the target
  while (sum * 2 <= target) {
    summands.push(sum);
    sum *= 2;
  }

  // Now add remaining terms (binary decomposition)
  let remaining = target - sum;
  let tempSummands = [...summands].reverse();

  for (const num of tempSummands) {
    if (num <= remaining) {
      summands.push(num);
      remaining -= num;
    }
  }

  if (remaining > 0) {
    summands.push(remaining);
  }

  return summands;
}

