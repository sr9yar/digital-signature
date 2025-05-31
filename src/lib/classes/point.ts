import { moduloPositive } from "../utility";
import { logger } from "./logger";



export class Point {

  logger = logger;
  x: number = 0;
  y: number = 0;

  constructor(x: number, y: number) {
    this.x = x;
    this.y = y;
  }

  toString() {
    const str = `(${this.x}, ${this.y})`
    // this.logger.log(str);
    return str;
  }

  /**
   * If point is equal to another point
   * @param point2 
   * @returns 
   */
  equals(point2: Point): boolean {
    if (
      point2.x === this.x &&
      point2.y === this.y) {
      return true;
    }
    return false;
  }

  /**
   * If point is equal to inverse of another point
   * @param point2 
   * @returns 
   */
  equalsInverse(point2: Point): boolean {
    if (
      point2.x === this.x &&
      -point2.y === this.y
    ) {
      return true;
    }
    return false;
  }

  /**
   * checks if two poits in an elliptic curve are
   * mutullay inverse (their addition results 
   * in the identity element - the point at infinity)
   * @param point2 
   * @param modulo p
   */
  areMutuallyInverse(point2: Point, p: number = 1): boolean {
    if (
      moduloPositive(point2.x, p) === moduloPositive(this.x, p) &&
      point2.y !== this.y &&
      Math.abs(point2.y) === Math.abs(this.y)
    ) {
      return true;
    }
    return false;

  }

  /**
   * is zero
   */
  get is0(): boolean {
    return this.x === 0 && this.y === 0;
  }
}


