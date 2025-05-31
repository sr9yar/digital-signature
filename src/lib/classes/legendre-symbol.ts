
import {
  isPrime,
  modulo,
  modulo2,
  primeFactors,
  tt,
} from '../utility';



import { LoggerType } from '../types/logger.type';
import { logger } from './logger';



/**
 * Нахождение символа лежандра (a/p)
 */
export class LegendreSymbol {

  // logger
  logger: LoggerType = logger;
  //
  public a: number = 0;
  //
  public p: number = 0;

  // -1 | 0 | 1 
  symbol: number = 0;

  // https://www.mymathtables.com/numbers/legendre-symbol-generator.html
  constructor(a?: number, p?: number) {
    if (typeof a === 'number') {
      this.a = a;
    }
    if (typeof p === 'number') {
      this.p = p;
    }
  }



  /**
   * Вычисление символа Лежандра
   * 
   * @returns 
   */
  calc(a?: number, p?: number): number {

    a = a ?? this.a;
    p = p ?? this.p;

    this.logger.log(`▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ ▽ `, 'color:gray');
    this.logger.log(`Вычисление символа Лежандра.`);
    this.logger.log(`a=${a}, p=${p}`);
    this.logger.log(` `);
    this.logger.log(`- - - - - - - - - - - - - - - - - - - - - - - - - - - - - -`, 'color:gray');
    this.logger.log(`x² ≡ a (mod p), p>1, a ∈ {1, 2, p-1}`, 'color:gray');
    this.logger.log(`  или в виде символа Лежандра`, 'color:gray');
    this.logger.log(`Существует два варианта: `, 'color:gray');
    this.logger.log(`(a/p) = +1 ← квадратичный вычет`, 'color:gray');
    this.logger.log(`(a/p) = -1 ← квадратичный невычет`, 'color:gray');
    this.logger.log(` `);
    // https://mathcenter.oxford.emory.edu/site/math125/legendresSymbolProperties/
    this.logger.log(`Свойства символа Лежандра`, 'color:gray');
    this.logger.log(`1. (a²/p) = 1`, 'color:gray');
    this.logger.log(`2. (-1/p) = p mod 4`, 'color:gray');
    this.logger.log(`3. (2/p) = { 1, если p ≡ ±1 mod 8}`, 'color:gray');
    this.logger.log(`   (2/p)   {-1, если p ≡ ±3 mod 8}`, 'color:gray');
    this.logger.log(`4. (a/p) = ( (a₁ * a₂ * a₃ ... * aₖ)/p ) = (a₁/p)(a₂/p)(a₃/p) ... (aₖ/p)`, 'color:gray');
    this.logger.log(`5. a ≡ b (mod p), (a / p) = (b / p)`, 'color:gray');
    this.logger.log(`Критерий Эйлера: (a/p) = a^((p-1)/2) mod p`, 'color:gray');
    this.logger.log(`Квадратичный закон взаимности:`, 'color:gray');
    this.logger.log(`   (p/q)(q/p) = { 1, если p ≡ ±1 mod 4 либо q ≡ 1 mod 4}`, 'color:gray');
    this.logger.log(`                {-1, если p ≡ ±3 mod 4  и   q ≡ 3 mod 4}`, 'color:gray');
    this.logger.log(` `);
    this.logger.log(`- - - - - - - - - - - - - - - - - - - - - - - - - - - - - -`, 'color:gray');
    this.logger.log(` `);
    let symbol: number = 1;

    // if (a === 1) {
    //   this.logger.log(`Cимвол Лежандра вычислен: 1.\n`);
    //   return 1;
    // }

    // начинаем
    //
    // Определить является ли число простым или составным
    const numIsPrime = isPrime(a);
    if (a === -1) {
      this.logger.log(`Число a (${a}) = -1.`);
      symbol = this.useProperty2(a, p, 1);
    } else if (a === 2) {
      // Если a = 2 
      this.logger.log(`Число a (${a}) = 2.`);
      symbol = this.useProperty3(a, p, 1);
    } else if (numIsPrime) {
      // Если простое то используем квадратичный закон взаимности
      this.logger.log(`Число a (${a}) простое.`);
      symbol = this.useQuadraticReciprocityLaw(a, p, 1);
    } else {
      // Если не простое то используем свойство 4
      this.logger.log(`Число a (${a}) не является простым.`);
      symbol = this.useProperty4(a, p, 1);
    }

    this.logger.log(`Cимвол Лежандра вычислен: ${symbol}.\n`);
    this.symbol = symbol;
    return symbol;
  }



  /**
   * Property 1 of Legendre's Symbol
   * @param a number
   * @param p number
   * @returns number
   */
  useProperty1(a: number, p: number, t: number = 0): number {
    // this.logger.log(`1. (a²/p) = 1`);
    let symbol: number = 1;
    this.logger.log(`${tt(t)}Используем свойство 1 для (${a}²/${p}).`);

    this.logger.log(`${tt(t)}Символ Лежандра для (${a}²/${p}): ${symbol}.`);
    this.logger.log(`${tt(t)} `);
    return symbol;
  }



  /**
   * Property 2 of Legendre's Symbol
   * @param a number
   * @param p number
   * @returns number
   */
  useProperty2(a: number, p: number, t: number = 0): number {
    // this.logger.log(`2. (-1/p) = p mod 4`);
    let symbol: number = 1;
    this.logger.log(`${tt(t)}Используем свойство 2 для (${a}/${p}).`);

    const m = modulo2(p, 4);
    if (m[1] === 1) {
      symbol = 1;
    } else {
      symbol = m[0];
    }
    this.logger.log(`${tt(t)}(${a}/${p}) = {${p} mod 4} = ${symbol}`);

    this.logger.log(`${tt(t)}Символ Лежандра для (${a}/${p}): ${symbol}.`);
    this.logger.log(`${tt(t)} `);
    return symbol;
  }



  /**
   * Property 3 of Legendre's Symbol
   * @param a number
   * @param p number
   * @returns number
   */
  useProperty3(a: number, p: number, t: number = 0): number {
    // this.logger.log(`3. (2/p) = { 1, если p ≡ ±1 mod 8}`);
    // this.logger.log(`   (2/p)   {-1, если p ≡ ±3 mod 8}`);

    let symbol: number = 1;

    this.logger.log(`${tt(t)}Используем свойство 3 для (${a}/${p}).`);

    const moduli = modulo2(p, 8);



    if (moduli.includes(3)) {
      this.logger.log(`${tt(t)}(${a}/${p}) = {${p} mod 8 = 3} = -1`);
      symbol = -1;
    }

    else if (moduli.includes(1)) {
      this.logger.log(`${tt(t)}(${a}/${p}) = {${p} mod 8 = 1} = 1`);
      symbol = 1;
    }

    else if (moduli.includes(-1)) {
      this.logger.log(`${tt(t)}(${a}/${p}) = {${p} mod 8 = -1} = 1`);
      symbol = 1;
    }

    else if (moduli.includes(-3)) {
      this.logger.log(`${tt(t)}(${a}/${p}) = {${p} mod 8 = -3} = -1`);
      symbol = -1;
    }



    this.logger.log(`${tt(t)}Следовательно символ Лежандра для (${a}/${p}): ${symbol}.`);
    this.logger.log(`${tt(t)} `);
    return symbol;
  }



  /**
   * Property 4 of Legendre's Symbol
   * Разложить а на простые числа - получить несколько символов Лежандра
   * @param a number
   * @param p number
   * @returns number
   */
  useProperty4(a: number, p: number, t: number = 0): number {
    // this.logger.log(`4. (a/p) = ( (a₁ * a₂ * a₃ ... * aₖ)/p ) = (a₁/p)(a₂/p)(a₃/p) ... (aₖ/p)`);
    let symbols: number[] = [];

    this.logger.log(`${tt(t)}Используем свойство 4 для (${a}/${p}).`);
    this.logger.log(`${tt(t)} `);

    const factors = primeFactors(a);
    this.logger.log(`${tt(t)}Раскладываем ${a} на делители: ${factors.join()}`);

    let list: string[] = []
    for (let i = 0; i < factors.length; i++) {
      list.push(`(${factors[i]}/${p})`);
    }
    this.logger.log(`${tt(t)}(${a}/${p}) = ((${factors.join('*')})/${p}) = ${list.join('*')}`);
    this.logger.log(`${tt(t)} `);

    for (let i = 0; i < factors.length; i++) {
      const f = factors[i];
      let s: number = 0;
      if (f === 2) {
        s = this.useProperty3(f, p, t + 1);
      } else if (isPrime(f)) {
        s = this.useQuadraticReciprocityLaw(f, p, t + 1);
      } else if (!isPrime(f)) {
        s = this.useProperty4(a, p, t + 1);
      }
      if (s) {
        symbols.push(s);
        continue;
      }
      this.logger.error(`f=${f} что делать-то? 😱`);
    }


    const symbol = symbols.reduce((a, c) => a * c, 1);

    this.logger.log(`${tt(t)}Умножаем символы для ${list.join('')} = ${symbols.join('*')} = ${symbol}`);

    return symbol;
  }



  /**
   * Квадратичный закон взаимности
   * Определение можно ли перевернуть символ без изменения знака
   * @param a 
   * @param p 
   * @returns 
   */
  useQuadraticReciprocityLaw(p: number, q: number, t: number = 0): number {
    // this.logger.log(`Квадратичный закон взаимности:`);
    // this.logger.log(`   (p/q)(q/p) = { 1, если p ≡ ±1 mod 4 либо q ≡ 1 mod 4}`);
    // this.logger.log(`                {-1, если p ≡ ±3 mod 4  и   q ≡ 3 mod 4}`);

    this.logger.log(`${tt(t)}Используем квадратичный закон взаимности для (${p}/${q}). p=${p}, q=${q}`);

    const pad = (p > q ? p : q).toString().length;
    let symbol: number = 1;

    const moduliP = modulo2(p, 4);
    const moduliQ = modulo2(q, 4);
    // this.logger.log(`${tt(t)}⎰ ${p.pad(pad)} mod 4 = ${moduliP[0]}⎱`);
    // this.logger.log(`${tt(t)}⎱ ${q.pad(pad)} mod 4 = ${moduliQ[0]}⎰`);
    this.logger.log(`${tt(t)}⎰ ${p.toFixed().padStart(pad)} mod 4 = ${moduliP[0]}⎱`);
    this.logger.log(`${tt(t)}⎱ ${q.toFixed().padStart(pad)} mod 4 = ${moduliQ[0]}⎰`);

    // to reverse sign multiplicator
    let reverseSign: number = 1;

    const pMinusThree = moduliP.includes(-3);
    const pThree = moduliP.includes(3);
    const qThree = moduliQ.includes(3);

    const pMinusOne = moduliP.includes(-1);
    const pOne = moduliP.includes(1);
    const qOne = moduliQ.includes(1);

    if (pThree && qThree) { // if ((pThree || pMinusThree) && qThree) {
      this.logger.log(`${tt(t)}При перевороте необходимо сменить знак символа: q = 3 mod 4, p = ${pMinusThree ? '-3' : '3'} mod 4.`);
      reverseSign = -1;
    } else if (pOne || qOne) { // } else if (pOne || pMinusOne || qOne) {
      // Если p или q равны 1
      // то по квадратичному закону взаимности 
      // можно перевернуть символ без смены знака
      this.logger.log(`${tt(t)}Можем перевернуть символ без смены знака: ${pOne ? 'p' : 'q'} mod 4 = ${pMinusOne ? '-1' : '1'}.`);
      reverseSign = 1;
    }

    const reversedQ = p;
    const reversedP = modulo(q, p);
    this.logger.log(`${tt(t)}Перевернутый символ: (${q}/${p}) = {${q} mod ${p} = ${reversedP}} = (${reversedP}/${reversedQ})`);

    if (reversedP === -1) {
      this.logger.log(`${tt(t)}p=${reversedP}.`);
      symbol = this.useProperty2(reversedP, reversedQ, t + 1);
    } if (reversedP === 1) {
      this.logger.log(`${tt(t)}p=${reversedP}. Можно представить как (1²/${reversedQ}).`);
      symbol = this.useProperty1(reversedP, reversedQ, t + 1);
    } else if (reversedP === 2) {
      this.logger.log(`${tt(t)}p=${reversedP}. Следовательно нужно применить свойство 3.`);
      symbol = this.useProperty3(reversedP, reversedQ, t + 1);
    } else if (!isPrime(reversedP)) {
      this.logger.log(`${tt(t)}p не является простым числом. p=${reversedP}. Следовательно нужно применить свойство 4.`);
      symbol = this.useProperty4(reversedP, reversedQ, t + 1);
    } else {
      this.logger.log(`${tt(t)}Символ можно перевернуть еще раз. p=${reversedP}.`);
      symbol = this.useQuadraticReciprocityLaw(reversedP, reversedQ, t + 1);
    }

    symbol = symbol * reverseSign;
    this.logger.log(`${tt(t)}Следовательно символ Лежандра для (${p}/${q}): ${symbol}${reverseSign === -1 ? ' (знак перевернут)' : ''}.`);
    this.logger.log(`${tt(t)} `);

    return symbol;
  }



  /**
   * Print result
   */
  printResults(): void {
    this.logger.log(`The Legendre symbol: ${this.symbol}`, 'color:red');
  }



  /**
   * Run
   * @returns 
   */
  run() {
    this.calc(this.a, this.p);
    this.printResults();
    return this.symbol;
  }

}
