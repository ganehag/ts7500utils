/* Copyright 2009-2010, Unpublished Work of Technologic Systems
 * All Rights Reserved.
 *
 * THIS WORK IS AN UNPUBLISHED WORK AND CONTAINS CONFIDENTIAL,
 * PROPRIETARY AND TRADE SECRET INFORMATION OF TECHNOLOGIC SYSTEMS.
 * ACCESS TO THIS WORK IS RESTRICTED TO (I) TECHNOLOGIC SYSTEMS 
 * EMPLOYEES WHO HAVE A NEED TO KNOW TO PERFORM TASKS WITHIN THE SCOPE
 * OF THEIR ASSIGNMENTS AND (II) ENTITIES OTHER THAN TECHNOLOGIC
 * SYSTEMS WHO HAVE ENTERED INTO APPROPRIATE LICENSE AGREEMENTS.  NO
 * PART OF THIS WORK MAY BE USED, PRACTICED, PERFORMED, COPIED, 
 * DISTRIBUTED, REVISED, MODIFIED, TRANSLATED, ABRIDGED, CONDENSED, 
 * EXPANDED, COLLECTED, COMPILED, LINKED, RECAST, TRANSFORMED, ADAPTED
 * IN ANY FORM OR BY ANY MEANS, MANUAL, MECHANICAL, CHEMICAL, 
 * ELECTRICAL, ELECTRONIC, OPTICAL, BIOLOGICAL, OR OTHERWISE WITHOUT
 * THE PRIOR WRITTEN PERMISSION AND CONSENT OF TECHNOLOGIC SYSTEMS.
 * ANY USE OR EXPLOITATION OF THIS WORK WITHOUT THE PRIOR WRITTEN
 * CONSENT OF TECHNOLOGIC SYSTEMS COULD SUBJECT THE PERPETRATOR TO
 * CRIMINAL AND CIVIL LIABILITY.
 */


/*******************************************************************************
* Program: 
*    Get DIO (dio.c)
*    Technologic Systems TS-7500 with TS-752 Development Board
* 
* Summary:
*   This program will accept any pin number between 5 and 40 and attempt to get
* or set those pins in a c program rather than scripted.  You will need the 
* TS-7500 and TS-752 development board. Although this program will enable the 
* use of said pins, it will primarily enable the use of the 8 Inputs, 3 Outputs,
* and Relays on the TS-752.  Keep in mind that if a GND or PWR pin is read (or
* something else unlogical, we don't necessarily care about the output because 
* it could be simply "junk". 
*   Notice careful semaphore usage (sbuslock, sbusunlock) within main.
*
* Usage:
*   ./dio <get|set> <pin#> <set_value (0|1|2)>
*
* 0 - GND
* 1 - 3.3V
* 2 - Z (High Impedance)
*
* Examples:
*   To read an input pin (such as 1 through 8 on the TS-752):
*      ts7500:~/sbus# ./dio get 40
*      Result of getdiopin(38) is: 1 
*
*   To set an output pin (such as 1 through 3 or relays on the TS-752):
*      ts7500:~/sbus# ./dio set 33 0
*      Pin#33 has been set to 0   [You may verify with DVM]
*
* Compile with:
*   gcc -mcpu=arm9 dio.c sbus.c -o dio
*
* Version history:
*  12/09/2009 - DH
*    Initial revision
*  12/16/2010 - KB
*    Updated for new sbus.c API
*******************************************************************************/
#include "sbus.h"
#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

#define DIO_Z 2

/*******************************************************************************
* setdiopin: accepts a DIO register and value to place in that DIO pin.
*   Values can be 0 (low), 1 (high), or 2 (z - high impedance).
*******************************************************************************/
void setdiopin(int pin, int val)
{
   int pinOffSet;
   int dirPinOffSet; // For Register 0x66 only
   int outPinOffSet; // For Register 0x66 only

   // First, check for the high impedance case
   if (val == 2)
   {
      if (pin <= 40 && pin >= 37)
      {
         dirPinOffSet = pin - 33;
         sbus_poke16(0x66, sbus_peek16(0x66) & ~(1 << dirPinOffSet));
      }
      else if (pin <= 36 && pin >= 21)
      {
         pinOffSet = pin - 21;
         sbus_poke16(0x6c, sbus_peek16(0x6c) & ~(1 << pinOffSet));
      }
      else if (pin <= 20 && pin >= 5)
      {
         pinOffSet = pin - 5;
         sbus_poke16(0x72, sbus_peek16(0x72) & ~(1 << pinOffSet));
      }
   }

   /******************************************************************* 
   *0x66: DIO and tagmem control (RW)
   *  bit 15-12: DIO input for pins 40(MSB)-37(LSB) (RO)
   *  bit 11-8: DIO output for pins 40(MSB)-37(LSB) (RW)
   *  bit 7-4: DIO direction for pins 40(MSB)-37(LSB) (1 - output) (RW)
   ********************************************************************/
   else if (pin <= 40 && pin >= 37)
   {
      dirPinOffSet = pin - 33; // -37 + 4 = Direction; -37 + 8 = Output
      outPinOffSet = pin - 29;

      // set bit [pinOffset] to [val] of register [0x66] 
      if(val)
         sbus_poke16(0x66, (sbus_peek16(0x66) | (1 << outPinOffSet)));
      else
         sbus_poke16(0x66, (sbus_peek16(0x66) & ~(1 << outPinOffSet)));

      // Make the specified pin into an output in direction bits
      sbus_poke16(0x66, sbus_peek16(0x66) | (1 << dirPinOffSet)); ///

   }

   /********************************************************************* 
   *0x68: DIO input for pins 36(MSB)-21(LSB) (RO)    
   *0x6a: DIO output for pins 36(MSB)-21(LSB) (RW)
   *0x6c: DIO direction for pins 36(MSB)-21(LSB) (1 - output) (RW)
   *********************************************************************/
   else if (pin <= 36 && pin >= 21)
   {
      pinOffSet = pin - 21;

      // set bit [pinOffset] to [val] of register [0x6a] 
      if(val)
         sbus_poke16(0x6a, (sbus_peek16(0x6a) | (1 << pinOffSet)));
      else
         sbus_poke16(0x6a, (sbus_peek16(0x6a) & ~(1 << pinOffSet)));

      // Make the specified pin into an output in direction register
      sbus_poke16(0x6c, sbus_peek16(0x6c) | (1 << pinOffSet)); ///
   }

   /********************************************************************* 
   *0x6e: DIO input for pins 20(MSB)-5(LSB) (RO)    
   *0x70: DIO output for pins 20(MSB)-5(LSB) (RW)
   *0x72: DIO direction for pins 20(MSB)-5(LSB) (1 - output) (RW)
   *********************************************************************/
   else if (pin <= 20 && pin >= 5)
   {
      pinOffSet = pin - 5;

      if(val)
         sbus_poke16(0x70, (sbus_peek16(0x70) | (1 << pinOffSet)));
      else
         sbus_poke16(0x70, (sbus_peek16(0x70) & ~(1 << pinOffSet)));

      // Make the specified pin into an output in direction register
      sbus_poke16(0x72, sbus_peek16(0x72) | (1 << pinOffSet));
   }

}


/*******************************************************************************
* getdiopin: accepts a DIO pin number and returns its value.  
*******************************************************************************/
int getdiopin(int pin)
{
   int pinOffSet;
   int pinValue = 99999;

   /******************************************************************* 
   *0x66: DIO and tagmem control (RW)
   *  bit 15-12: DIO input for pins 40(MSB)-37(LSB) (RO)
   *  bit 11-8: DIO output for pins 40(MSB)-37(LSB) (RW)
   *  bit 7-4: DIO direction for pins 40(MSB)-37(LSB) (1 - output) (RW)
   ********************************************************************/
   if (pin <= 40 && pin >= 37)
   {
      pinOffSet = pin - 25; // -37 to get to 0, + 10 to correct offset

      // Obtain the specific pin value (1 or 0)
      pinValue = (sbus_peek16(0x66) >> pinOffSet) & 0x0001;
   }

   /*********************************************************************   
   *0x68: DIO input for pins 36(MSB)-21(LSB) (RO)  
   *0x6a: DIO output for pins 36(MSB)-21(LSB) (RW)
   *0x6c: DIO direction for pins 36(MSB)-21(LSB) (1 - output) (RW)
   *********************************************************************/
   else if (pin <= 36 && pin >= 21)
   {
      pinOffSet = pin - 21; // Easier to understand when LSB = 0 and MSB = 15

      // Obtain the specific pin value (1 or 0)
      pinValue = (sbus_peek16(0x68) >> pinOffSet) & 0x0001;
   }

   /*********************************************************************   
   *0x6e: DIO input for pins 20(MSB)-5(LSB) (RO)  
   *0x70: DIO output for pins 20(MSB)-5(LSB) (RW)
   *0x72: DIO direction for pins 20(MSB)-5(LSB) (1 - output) (RW)
   *********************************************************************/
   else if (pin <= 20 && pin >= 5)
   {
      pinOffSet = pin - 5;  // Easier to understand when LSB = 0 and MSB = 15

      // Obtain the specific pin value (1 or 0)
      pinValue = (sbus_peek16(0x6e) >> pinOffSet) & 0x0001;
   }
   return pinValue;
}



/*******************************************************************************
* Main: accept input from the command line and act accordingly.
*******************************************************************************/
int main(int argc, char **argv)
{
   int pin;
   int val;
   int returnedValue;
         
   // Check for invalid command line arguments
   if ((argc > 4) | (argc < 3))
   {
       printf("Usage: %s <get|set> <pin#> <set_value (0|1|2)>\n* 0 - GND\n* 1 - 3.3V\n* 2 - Z (High Impedance)\n", argv[0]);
       return 1;
   }
   
   // We only want to get val if there are more than 3 command line arguments
   if (argc == 3)
      pin = strtoul(argv[2], NULL, 0);
   else
   {
      pin = strtoul(argv[2], NULL, 0);
      val = strtoul(argv[3], NULL, 0);
   }
   
   // If anything other than pins 5 through 40, fail program
   assert(pin <= 40 && pin >= 5);

   // Parse through the command line arguments, check for valid inputs, and exec
   if (!(strcmp(argv[1], "get")) && (argc == 3))
   {
      sbuslock();
      returnedValue = getdiopin(pin);
      sbusunlock();
      
      printf("pin#%d = %d \n", pin, returnedValue);
   }
   else if(!(strcmp(argv[1], "set")) && (argc == 4) && (val <= 2))
   {
      sbuslock();
      setdiopin(pin, val);
      sbusunlock();
      
      printf("pin#%d set to %d\n", pin, val);
   }   
   else
   {
      printf("Usage: %s <get|set> <pin#> <set_value (0|1|2)>\n* 0 - GND\n* 1 - 3.3V\n* 2 - Z (High Impedance)\n", argv[0]);
      return 1;
   }
   return 0;
}
