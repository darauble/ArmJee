// RFM12B STM32F103 CMSIS driver implementation

//Based on 2009-02-09 <jcw@equi4.com> http://opensource.org/licenses/mit-license.php
//It is also based on the MSP430 port of the jeenode library: https://github.com/simpleavr/MSPNode.git
//implements basic jeeNode functions

#include <string.h>

#include "RF12.h"
#include "stm32f10x.h"

#include "debug_uart.h"

// maximum transmit / receive buffer: 3 header + data + 2 crc bytes
#define RF_MAX   (RF12_MAXDATA + 5)

/* SPI CONFIGURATION: */
#define SPI_NUM   1

#if SPI_NUM == 1
	#define SPI_HW   SPI1
#elif SPI_NUM == 2
	#define SPI_HW   SPI2
#endif

// Software SS, defined separately
#define SS_PORT  GPIOA  // the port the SS pin is on  (GPIOA for SPI1, GPIOB for SPI2 on STM32F103)
#define SS_BIT_HI   GPIO_BSRR_BS4      // This is the same as the hardware SS pn (4 on SPI1, 12 on SPI2 on STM32F103)
#define SS_BIT_LO   GPIO_BSRR_BR4      // This is the same as the hardware SS pn (4 on SPI1, 12 on SPI2 on STM32F103)
#define SS_PIN_INIT \
	RCC->APB2ENR |= RCC_APB2ENR_IOPAEN; \
	SS_PORT->CRL &= ~(GPIO_CRL_CNF4 | GPIO_CRL_MODE4 ); \
	SS_PORT->CRL |= GPIO_CRL_MODE4;  /* General purpose push-pull (CNF 00), 50 MHz (MODE 11) */

// Interrupt pin
#define IRQ_PORT GPIOB
#define IRQ_PIN_READ GPIO_IDR_IDR0
#define IRQ_PIN_INIT \
		RCC->APB2ENR |= RCC_APB2ENR_IOPBEN; \
		IRQ_PORT->CRL &= ~(GPIO_CRL_CNF0 | GPIO_CRL_MODE0); \
		IRQ_PORT->CRL |= GPIO_CRL_CNF0_1; /* Input pull-up-down */ \
		IRQ_PORT->BSRR |= GPIO_BSRR_BS0; /* Pull-up */

#define IRQ_INIT_EXTI_LINE \
		AFIO->EXTICR[0] &= ~(0x0F); /* Clear EXTI0 */ \
		AFIO->EXTICR[0] |= AFIO_EXTICR1_EXTI0_PB; /* Source GPIOB */

#define IRQ_INIT_EXTI \
		EXTI->IMR |= EXTI_IMR_MR0; /* Line 0, i.e. pin0, enable Interrup Mask */ \
		EXTI->FTSR |=  EXTI_FTSR_TR0; /* Trigger on falling edge */

#define IRQ_PIN_IRQn EXTI0_IRQn
#define IRQ_PIN_ISR EXTI0_IRQHandler
#define IRQ_ENABLE NVIC->ISER[IRQ_PIN_IRQn >> 0x05] = (uint32_t)0x01 << (IRQ_PIN_IRQn & (uint8_t)0x1F);
#define IRQ_DISABLE NVIC->ICER[IRQ_PIN_IRQn >> 0x05] = (uint32_t)0x01 << (IRQ_PIN_IRQn & (uint8_t)0x1F);

// RF12 command codes
#define RF_RECEIVER_ON  0x82DD
#define RF_XMITTER_ON   0x823D
#define RF_IDLE_MODE    0x820D
#define RF_SLEEP_MODE   0x8205
#define RF_WAKEUP_MODE  0x8207
#define RF_TXREG_WRITE  0xB800
#define RF_RX_FIFO_READ 0xB000
#define RF_WAKEUP_TIMER 0xE000
#define RF_STATUS_READ  0x0000

// RF12 status bits
#define RF_LBD_BIT      0x0400
#define RF_RSSI_BIT     0x0100

// bits in the node id configuration byte
#define NODE_BAND       0xC0        // frequency band
#define NODE_ACKANY     0x20        // ack on broadcast packets if set
#define NODE_ID         0x1F        // id of this node, as A..Z or 1..31

// transceiver states, these determine what to do with each interrupt
enum {
    TXCRC1, TXCRC2, TXTAIL, TXDONE, TXIDLE,
    TXRECV,
    TXPRE1, TXPRE2, TXPRE3, TXSYN1, TXSYN2,
};

static uint8_t nodeid;              // address of this node
static uint8_t group;               // network group
static volatile uint8_t rxfill;     // number of data bytes in rf12_buf
static volatile int8_t rxstate;     // current transceiver state

#define RETRIES     8               // stop retrying after 8 times
#define RETRY_MS    1000            // resend packet every second until ack'ed

static uint8_t ezInterval;          // number of seconds between transmits
static uint8_t ezSendBuf[RF12_MAXDATA]; // data to send
static char ezSendLen;              // number of bytes to send
static uint8_t ezPending;           // remaining number of retries
static long ezNextSend[2];          // when was last retry [0] or data [1] sent

volatile uint16_t rf12_crc;         // running crc value
volatile uint8_t rf12_buf[RF_MAX];  // recv/xmit buf, including hdr & crc bytes
volatile uint16_t rf12_statusbuf[RF_MAX];  // recv/xmit status buf
long rf12_seq;                      // seq number of encrypted packet (or -1)

static uint32_t seqNum;             // encrypted send sequence number
static uint32_t cryptKey[4];        // encryption key to use
void (*crypter)(uint8_t);           // does en-/decryption (null if disabled)

//Crc16 from https://github.com/simpleavr/MSPNode 
uint16_t _crc16_update(uint16_t crc, uint8_t a) {
	int i;
	crc ^= a;
	for (i=0;i<8;++i) {
		if (crc&0x0001)
			crc = (crc>>1) ^ 0xA001;
		else
			crc = (crc>>1);
	}
	return crc;
}

static uint8_t rf12_byte (uint8_t out) {  
	uint16_t outcmd=out;
	while ((SPI_HW->SR & SPI_SR_TXE) == 0);
	SPI_HW->DR = outcmd;
	while ((SPI_HW->SR & SPI_SR_RXNE) == 0);
	uint8_t outval8 = (uint8_t) (SPI_HW->DR & 0xFF);
	return outval8;
}

static uint16_t rf12_xfer (uint16_t cmd) {  //returns 16 bit int while sending a 16 bit int
	SS_PORT->BSRR |= SS_BIT_LO;
	while ((SPI_HW->SR & SPI_SR_TXE) == 0);
	SPI_HW->DR = cmd;
	while ((SPI_HW->SR & SPI_SR_RXNE) == 0);
	uint16_t reply = SPI_HW->DR;

	//snprintf(dbg_buf, DBG_BUF_LEN, "XFER: %04X %04X\r\n", cmd, reply);
	//dbg_print_buf();
	SS_PORT->BSRR |= SS_BIT_HI;

    return reply;

}
static void rf12_interrupt() { 
	uint16_t status = rf12_xfer(0x0000);

	if (rxstate == TXRECV) {  //if in recieve state
		uint8_t in = rf12_xfer(RF_RX_FIFO_READ);

		if (rxfill == 0 && group != 0){
			rf12_statusbuf[rxfill]=0;
			rf12_buf[rxfill++] = group;
		}

		rf12_statusbuf[rxfill]=status;
		rf12_buf[rxfill++] = in;
		rf12_crc = _crc16_update(rf12_crc, in);

		if (rxfill >= rf12_len + 5 || rxfill >= RF_MAX) {
			rf12_xfer(RF_IDLE_MODE);
		}
	} else {
		uint8_t out;

		if (rxstate < 0) {
			uint8_t pos = 3 + rf12_len + rxstate++;
			out = rf12_buf[pos];
			rf12_crc = _crc16_update(rf12_crc, out);
		} else {
			switch (rxstate++) {
				case TXSYN1: out = 0x2D; break;
				case TXSYN2: out = rf12_grp; rxstate = - (2 + rf12_len); break;
				case TXCRC1: out = rf12_crc; break;
				case TXCRC2: out = rf12_crc >> 8; break;
				case TXDONE: rf12_xfer(RF_IDLE_MODE); // fall through
				default:     out = 0xAA;
			}
		}
		rf12_xfer(RF_TXREG_WRITE + out);
	}
}

void rf12_spi_initialize () {
	RCC->APB2ENR |=  RCC_APB2ENR_AFIOEN;

	SS_PIN_INIT;

#if SPI_NUM == 1

	RCC->APB2ENR |= RCC_APB2ENR_IOPAEN;

	GPIOA->CRL &= ~(GPIO_CRL_CNF5 | GPIO_CRL_MODE5 | GPIO_CRL_CNF6 | GPIO_CRL_MODE6 | GPIO_CRL_CNF7 | GPIO_CRL_MODE7);
	GPIOA->CRL |=
			GPIO_CRL_CNF5_1 | GPIO_CRL_MODE5 // SPI1 Master SCK, Alternative push-pull, 50 MHz
			| GPIO_CRL_CNF6_0 // SPI1 Master MISO, Floating input
			| GPIO_CRL_CNF7_1 | GPIO_CRL_MODE7 // SPI1 Master MOSI, Alternative push-pull, 50 MHz
			;

	RCC->APB2ENR |= RCC_APB2ENR_SPI1EN;

	#define SPI_BAUDRATE (SPI_CR1_BR_2 | SPI_CR1_BR_0)

#elif SPI_NUM == 2
	RCC->APB2ENR |= RCC_APB2ENR_IOPBEN;

	GPIOB->CRH &= ~(GPIO_CRH_CNF13 | GPIO_CRH_MODE13 | GPIO_CRH_CNF14 | GPIO_CRH_MODE14 | GPIO_CRH_CNF15 | GPIO_CRH_MODE15);
	GPIOB->CRH |=
			GPIO_CRH_CNF13_1 | GPIO_CRH_MODE13 // SPI1 Master SCK, Alternative push-pull, 50 MHz
			| GPIO_CRH_CNF14_0 // SPI1 Master MISO, Floating input
			| GPIO_CRH_CNF15_1 | GPIO_CRH_MODE15 // SPI1 Master MOSI, Alternative push-pull, 50 MHz
			;

	RCC->APB1ENR |= RCC_APB1ENR_SPI2EN;

	#define SPI_BAUDRATE (SPI_CR1_BR_2)
#else
#error "Only SPI1 and SPI2 supported"
#endif

	SPI_HW->CR1 = 0;
	SPI_HW->CR1 |=
			SPI_CR1_DFF // 16 bit data frame
			| SPI_CR1_SSM | SPI_CR1_SSI // Software slave management, internal slave select
			| SPI_CR1_SPE // Enable SPI
			| SPI_BAUDRATE // Baud rate, div 32, 2.25 MHz
			| SPI_CR1_MSTR // Master
			;

    IRQ_PIN_INIT;
    IRQ_INIT_EXTI_LINE;
    IRQ_INIT_EXTI;

    NVIC->IP[IRQ_PIN_IRQn] = 0;
    IRQ_ENABLE;

    /*if ((IRQ_PORT->IDR & IRQ_PIN_READ) == 0) {
    	rf12_interrupt();
    }//*/
}

void IRQ_PIN_ISR()
{
	//dbg_print("RFM IRQ\r\n");
	rf12_interrupt();

	EXTI->PR = EXTI_PR_PR0;
}

// access to the RFM12B internal registers with rf12 interrupt disabled
uint16_t rf12_control(uint16_t cmd) {
	uint16_t retval;
	IRQ_DISABLE;
	retval = rf12_xfer(cmd);
	/* Since we can´t trigger RFM_IRQ to LOW and the Interrupt handler was disabled for some cycles
		a manual check is needed. A race condition should be impossible because rf12_interrupt is only triggered on FALLING LOW */
	if ((IRQ_PORT->IDR & IRQ_PIN_READ) == 0) {
		rf12_interrupt();
	}
	IRQ_ENABLE;

	return retval;
}


static void rf12_recvStart () {
	rxfill = rf12_len = 0;
	rf12_crc = ~0;
#if RF12_VERSION >= 2  
	if (group != 0)
		rf12_crc = _crc16_update(~0, group);
#endif
	rxstate = TXRECV;
	rf12_xfer(RF_RECEIVER_ON);
}

uint8_t rf12_recvDone () { 
	if (rxstate == TXRECV && (rxfill >= rf12_len + 5 || rxfill >= RF_MAX)) {
		rxstate = TXIDLE;
		if (rf12_len > RF12_MAXDATA)
			rf12_crc = 1; // force bad crc if packet length is invalid
		if (!(rf12_hdr & RF12_HDR_DST) || (nodeid & NODE_ID) == 31
			|| (rf12_hdr & RF12_HDR_MASK) == (nodeid & NODE_ID))
		{
			if (rf12_crc == 0 && crypter != 0)
				crypter(0);
			else
				rf12_seq = -1;
			return 1; // it's a broadcast packet or it's addressed to this node
		}
	}
	if (rxstate == TXIDLE) {
		rf12_recvStart();
	}
	return 0;
}

uint8_t rf12_canSend () {
    if (rxstate == TXRECV && rxfill == 0 &&
            ((rf12_xfer(RF_STATUS_READ)) & RF_RSSI_BIT) == 0) {
        rf12_control(RF_IDLE_MODE);
        rxstate = TXIDLE;
        rf12_grp = group;
        return 1;
    }
    return 0;
}

void rf12_sendStart_hdr (uint8_t hdr) {
    rf12_hdr = hdr & RF12_HDR_DST ? hdr :
                (hdr & ~RF12_HDR_MASK) + (nodeid & NODE_ID);
    if (crypter != 0)
        crypter(1);
    
    rf12_crc = ~0;
#if RF12_VERSION >= 2  //this is the state we are in
    rf12_crc = _crc16_update(rf12_crc, rf12_grp);  
#endif
    rxstate = TXPRE1; 
    //snprintf(dbg_buf, DBG_BUF_LEN, "TXPRE1: %d\r\n", rxstate);
    //dbg_print_buf();
    rf12_xfer(RF_XMITTER_ON); // bytes will be fed via interrupts
}

void rf12_sendStart(uint8_t hdr, const void* ptr, uint8_t len) {
    rf12_len = len;
    memcpy((void*) rf12_data, ptr, len);
    rf12_sendStart_hdr(hdr);
}

// deprecated
void rf12_sendStart_sync(uint8_t hdr, const void* ptr, uint8_t len, uint8_t sync) {
    rf12_sendStart(hdr, ptr, len);
    rf12_sendWait(sync);
}//*/

/// @details
/// Wait until transmission is possible, then start it as soon as possible.
/// @note This uses a (brief) busy loop and will discard any incoming packets.
/// @param hdr The header contains information about the destination of the
///            packet to send, and flags such as whether this should be
///            acknowledged - or if it actually is an acknowledgement.
/// @param ptr Pointer to the data to send as packet.
/// @param len Number of data bytes to send. Must be in the range 0 .. 65.
void rf12_sendNow (uint8_t hdr, const void* ptr, uint8_t len) {
  while (!rf12_canSend())
    rf12_recvDone(); // keep the driver state machine going, ignore incoming
  rf12_sendStart(hdr, ptr, len);
}

void rf12_sendWait (uint8_t mode) {
    // wait for packet to actually finish sending
    // go into low power mode, as interrupts are going to come in very soon
    //FIXME currently low power states are disabled for easier porting
    
    while (rxstate != TXIDLE);
    /*
        if (mode) {
            // power down mode is only possible if the fuses are set to start
            // up in 258 clock cycles, i.e. approx 4 us - else must use standby!
            // modes 2 and higher may lose a few clock timer ticks
            //set_sleep_mode(mode == 3 ? SLEEP_MODE_PWR_DOWN :
#ifdef SLEEP_MODE_STANDBY
                           //mode == 2 ? SLEEP_MODE_STANDBY :
#endif
                                       //SLEEP_MODE_IDLE);
            //sleep_mode();
        }
	*/
}

/*!
  Call this once with the node ID (0-31), frequency band (0-3), and
  optional group (0-255 for RF12B, only 212 allowed for RF12).
*/
void rf12_initialize (uint8_t id, uint8_t band, uint8_t g) {
    nodeid = id;
    group = g;
    
    uint32_t previousMillis = millis();
    uint32_t currentMillis = previousMillis;
    //previousMillis = millis();
    currentMillis = previousMillis;
    
    //spi_initialize();
	
    rf12_xfer(0x0000); // intitial SPI transfer added to avoid power-up problem !!!  

    rf12_xfer(RF_SLEEP_MODE); // DC (disable clk pin), enable lbd !!!
    
    // wait until RFM12B is out of power-up reset, this takes several *seconds*
    rf12_xfer(RF_TXREG_WRITE); // in case we're still in OOK mode
    while ( ((IRQ_PORT->IDR & IRQ_PIN_READ) == 0) && ((currentMillis - previousMillis) < 500) )
    {		
        rf12_xfer(RF_STATUS_READ);
        currentMillis = millis();   
    }
    if ((IRQ_PORT->IDR & IRQ_PIN_READ) == 0)
    {
      //SerialUSB.println("IRQ Error");
    }
    rf12_xfer(0x80C7 | (band << 4)); // EL (ena TX), EF (ena RX FIFO), 12.0pF 
    rf12_xfer(0xA640); // 868MHz    //this could be a problem as we use 433MHZ
    //rf12_xfer(0xA64C); // 868MHz    //this could be a problem as we use 433MHZ
    rf12_xfer(0xC606); // approx 49.2 Kbps, i.e. 10000/29/(1+6) Kbps
    //rf12_xfer(0x94A5); // VDI,FAST,134kHz,0dBm,-73dBm 
    //rf12_xfer(0x94A2); // VDI,FAST,134kHz,0dBm,-91dBm 
    //rf12_xfer(0x94A1); // VDI,FAST,134kHz,0dBm,-97dBm 
    rf12_xfer(0x94A2); // VDI,FAST,134kHz,0dBm,-103dBm 
    rf12_xfer(0xC2AC); // AL,!ml,DIG,DQD4 
    
    if (group != 0) {
        rf12_xfer(0xCA83); // FIFO8,2-SYNC,!ff,DR 
        rf12_xfer(0xCE00 | group); // SYNC=2DXX； 
    } else {
        rf12_xfer(0xCA8B); // FIFO8,1-SYNC,!ff,DR 
        rf12_xfer(0xCE2D); // SYNC=2D； 
    }
    rf12_xfer(0xC483); // @PWR,NO RSTRIC,!st,!fi,OE,EN 
    rf12_xfer(0x9850); // !mp,90kHz,MAX OUT 
    rf12_xfer(0xCC77); // OB1，OB0, LPX,！ddy，DDIT，BW0 
    rf12_xfer(0xE000); // NOT USE 
    rf12_xfer(0xC800); // NOT USE 
    rf12_xfer(0xC049); // 1.66MHz,3.1V 

    rxstate = TXIDLE;
    
    if ((nodeid & NODE_ID) != 0){
    	IRQ_ENABLE;
	}
    else {
    	IRQ_DISABLE;
    }
}

void rf12_onOff (uint8_t value) {
    rf12_xfer(value ? RF_XMITTER_ON : RF_IDLE_MODE);
}

uint8_t rf12_config (uint8_t show) {
    //~ //crc check the rf12 settings preset in the avr internal eeprom
    //~ uint16_t crc = ~0;
    //~ for (uint8_t i = 0; i < RF12_EEPROM_SIZE; ++i)
        //~ crc = _crc16_update(crc, eeprom_read_byte(RF12_EEPROM_ADDR + i));
    //~ if (crc != 0)
        //~ return 0; //exit if bad crc
    
    //~ //read node and group id out of the internal avr eeprom    
    //~ uint8_t nodeId = 0, group = 0;
    //~ for (uint8_t i = 0; i < RF12_EEPROM_SIZE - 2; ++i) {
        //~ uint8_t b = eeprom_read_byte(RF12_EEPROM_ADDR + i);
        //~ if (i == 0)
            //~ nodeId = b;
        //~ else if (i == 1)
            //~ group = b;
        //~ else if (b == 0)
            //~ break;
        //~ else if (show)
            //~//SerialUSB.print(b);
    //~ }
    //~ if (show)
        //~//SerialUSB.println();
    uint8_t nodeId = 1; //FIXME only uses node ID 1
    //uint8_t group = 212;  //only possible group for rfm12, also optional so leave it for now
    rf12_initialize(nodeId, nodeId >> 6, group);
    return nodeId & RF12_HDR_MASK;
}

void rf12_sleep (char n) {
    if (n < 0)
        rf12_control(RF_IDLE_MODE);
    else {
        rf12_control(RF_WAKEUP_TIMER | 0x0500 | n);
        rf12_control(RF_SLEEP_MODE);
        if (n > 0)
            rf12_control(RF_WAKEUP_MODE);
    }
    rxstate = TXIDLE;
}

char rf12_lowbat () {
    return (rf12_control(0x0000) & RF_LBD_BIT) != 0;
}

void rf12_easyInit (uint8_t secs) {
    ezInterval = secs;
}

char rf12_easyPoll () {
    if (rf12_recvDone() && rf12_crc == 0) {
        unsigned char myAddr = nodeid & RF12_HDR_MASK;
        if (rf12_hdr == (RF12_HDR_CTL | RF12_HDR_DST | myAddr)) {
            ezPending = 0;
            ezNextSend[0] = 0; // flags succesful packet send
            if (rf12_len > 0)
                return 1;
        }
    }
    if (ezPending > 0) {
        // new data sends should not happen less than ezInterval seconds apart
        // ... whereas retries should not happen less than RETRY_MS apart
        unsigned char newData = ezPending == RETRIES;
        long now = millis();
        if (now >= ezNextSend[newData] && rf12_canSend()) {
            ezNextSend[0] = now + RETRY_MS;
            // must send new data packets at least ezInterval seconds apart
            // ezInterval == 0 is a special case:
            //      for the 868 MHz band: enforce 1% max bandwidth constraint
            //      for other bands: use 100 msec, i.e. max 10 packets/second
            if (newData)
                ezNextSend[1] = now +
                    (ezInterval > 0 ? 1000L * ezInterval
                                    : (nodeid >> 6) == RF12_868MHZ ?
                                            13 * (ezSendLen + 10) : 100);
            rf12_sendStart(RF12_HDR_ACK, ezSendBuf, ezSendLen);
            --ezPending;
        }
    }
    return ezPending ? -1 : 0;
}

char rf12_easySend (const void* data, uint8_t size) {
    if (data != 0 && size != 0) {
        if (ezNextSend[0] == 0 && size == ezSendLen &&
                                    memcmp(ezSendBuf, data, size) == 0)
            return 0;
        memcpy(ezSendBuf, data, size);
        ezSendLen = size;
    }
    ezPending = RETRIES;
    return 1;
}

// XXTEA by David Wheeler, adapted from http://en.wikipedia.org/wiki/XXTEA

//~ #define DELTA 0x9E3779B9
//~ #define MX (((z>>5^y<<2) + (y>>3^z<<4)) ^ ((sum^y) + \
                                            //~ (cryptKey[(uint8_t)((p&3)^e)] ^ z)))

//~ static void cryptFun (uint8_t send) {
    //~ uint32_t y, z, sum, *v = (uint32_t*) rf12_data;
    //~ uint8_t p, e, rounds = 6;
    //~ 
    //~ if (send) {
        //~ // pad with 1..4-byte sequence number
        //~ *(uint32_t*)(rf12_data + rf12_len) = ++seqNum;
        //~ uint8_t pad = 3 - (rf12_len & 3);
        //~ rf12_len += pad;
        //~ rf12_data[rf12_len] &= 0x3F;
        //~ rf12_data[rf12_len] |= pad << 6;
        //~ ++rf12_len;
        //~ // actual encoding
        //~ char n = rf12_len / 4;
        //~ if (n > 1) {
            //~ sum = 0;
            //~ z = v[n-1];
            //~ do {
                //~ sum += DELTA;
                //~ e = (sum >> 2) & 3;
                //~ for (p=0; p<n-1; p++)
                    //~ y = v[p+1], z = v[p] += MX;
                //~ y = v[0];
                //~ z = v[n-1] += MX;
            //~ } while (--rounds);
        //~ }
    //~ } else if (rf12_crc == 0) {
        //~ // actual decoding
        //~ char n = rf12_len / 4;
        //~ if (n > 1) {
            //~ sum = rounds*DELTA;
            //~ y = v[0];
            //~ do {
                //~ e = (sum >> 2) & 3;
                //~ for (p=n-1; p>0; p--)
                    //~ z = v[p-1], y = v[p] -= MX;
                //~ z = v[n-1];
                //~ y = v[0] -= MX;
            //~ } while ((sum -= DELTA) != 0);
        //~ }
        //~ // strip sequence number from the end again
        //~ if (n > 0) {
            //~ uint8_t pad = rf12_data[--rf12_len] >> 6;
            //~ rf12_seq = rf12_data[rf12_len] & 0x3F;
            //~ while (pad-- > 0)
                //~ rf12_seq = (rf12_seq << 8) | rf12_data[--rf12_len];
        //~ }
    //~ }
//~ }

//~ void rf12_encrypt (const uint8_t* key) {
    //~ // by using a pointer to cryptFun, we only link it in when actually used
    //~ if (key != 0) {
        //~ for (uint8_t i = 0; i < sizeof cryptKey; ++i)
            //~ ((uint8_t*) cryptKey)[i] = eeprom_read_byte(key + i);
        //~ crypter = cryptFun;
    //~ } else
        //~ crypter = 0;
   //~ //
//~ }
