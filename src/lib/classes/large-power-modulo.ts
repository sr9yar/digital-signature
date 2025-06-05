import { LoggerType } from '../types/logger.type';
import {
  modulo,
  sup
} from '../utility';
import { logger } from './logger';


/**
 * n  - number
 * a  - power
 * p  - modulo
 */
export class LargePowerModulo {

  // allows to use a customer logger
  logger: LoggerType = logger;

  // n number
  private n: number = 1;
  // a power 
  private a: number = 1;
  // p modulo 
  private p: number = 1;

  constructor(n?: number, a?: number, p?: number) {
    if (typeof n === 'number') {
      this.n = n;
    }
    if (typeof a === 'number') {
      this.a = a;
    }
    if (typeof p === 'number') {
      this.p = p;
    }
  }


  /**
   * Compute large power of 2 modulo p
   * n^a mod p
   *
   * check
   * 3 ^ 119 mod 953 = 797
   * 221 ^ 60 mod 953 = 256
   * test: https://www.boxentriq.com/code-breaking/modular-exponentiation
   * 
   * @param n number
   * @param a power 
   * @param p modulo
   * @returns [r - result]
   */
  calc(n?: number, a?: number, p?: number): [number, number[], number[], number[]] {

    if (n === 0) {
      return [0, [], [], []];
    }

    n = n ?? this.n;
    a = a ?? this.a;
    p = p ?? this.p;

    // line k - reverse binary representation of the power
    const k = a.toString(2).split('').map(Number).reverse();

    const A = Array(k.length);
    const b = Array(k.length);
    let r: number = 0;
    b[0] = 1;
    A[0] = n;
    if (k[0] === 1) {
      b[0] = n;
    }
    for (let i = 1; i < k.length; i++) {
      const bPrev = b[i - 1] ?? 1;
      const Ai = modulo(A[i - 1] ** 2, p);
      A[i] = Ai;
      if (k[i] === 1) {
        b[i] = modulo(Ai * bPrev, p);
      } else {
        b[i] = bPrev;

      }
    }

    // answer
    r = b[k.length - 1];

    return [r, k, A, b];
  }




  /**
   * Get results
   * @param n 
   * @param a 
   * @param p 
   */
  getResults(): [number, number[], number[], number[]] {
    return this.calc(this.n, this.a, this.p);
  }



  /**
   * Print results
   * @param n 
   * @param a 
   * @param p 
   */
  printResults(): [number, number[], number[], number[]] {

    this.logger.log(`Возводим ${this.n} в степень ${this.a} по модулю ${this.p}.`);
    const [r, k, A, b] = this.calc(this.n, this.a, this.p);
    this.logger.log(`${k.join('\t')}`, 'color:yellow');
    this.logger.log(`${A.join('\t')}`, 'color:yellow');
    this.logger.log(`${b.join('\t')}`, 'color:yellow');
    this.logger.log(`Ответ: ${r}`, 'color:yellow');
    this.logger.log(`${this.n}${sup(this.a)} mod ${this.p} = ${r}`);
    this.logger.log(``);
    return [r, k, A, b];
  }


}