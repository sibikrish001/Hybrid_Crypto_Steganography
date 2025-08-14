// Global variables to store encryption state
let encryptionState = {
    plainText: '',
    hillEncrypted: '',
    sdesEncrypted: '',
    coverImageData: null,
    stegoImageData: null,
    extractedMessage: '',
    sdesDecrypted: '',
    finalDecrypted: ''
};

// Hill Cipher Implementation
class HillCipher {
    constructor(keyMatrix) {
        this.keyMatrix = keyMatrix;
        this.MOD = 26;
    }

    static validateKey(matrix) {
        const det = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
        const detMod = ((det % 26) + 26) % 26;
        return this.gcd(detMod, 26) === 1;
    }

    static gcd(a, b) {
        while (b !== 0) {
            const temp = b;
            b = a % b;
            a = temp;
        }
        return a;
    }

    static modInverse(a, m) {
        for (let i = 1; i < m; i++) {
            if ((a * i) % m === 1) return i;
        }
        return -1;
    }

    static matrixInverse(matrix, mod) {
        const det = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
        const detMod = ((det % mod) + mod) % mod;
        const detInv = this.modInverse(detMod, mod);
        
        if (detInv === -1) return null;
        
        return [
            [((matrix[1][1] * detInv) % mod + mod) % mod, ((-matrix[0][1] * detInv) % mod + mod) % mod],
            [((-matrix[1][0] * detInv) % mod + mod) % mod, ((matrix[0][0] * detInv) % mod + mod) % mod]
        ];
    }

    stringToNumbers(text) {
        return text.toUpperCase().replace(/[^A-Z]/g, '').split('').map(char => char.charCodeAt(0) - 65);
    }

    numbersToString(numbers) {
        return numbers.map(num => String.fromCharCode(num + 65)).join('');
    }

    encrypt(plaintext) {
        const numbers = this.stringToNumbers(plaintext);
        const originalLength = numbers.length;
        
        if (numbers.length % 2 !== 0) {
            numbers.push(0); // Add 'A' padding
        }

        const encrypted = [];
        for (let i = 0; i < numbers.length; i += 2) {
            const vector = [numbers[i], numbers[i + 1]];
            const result = [
                (this.keyMatrix[0][0] * vector[0] + this.keyMatrix[0][1] * vector[1]) % this.MOD,
                (this.keyMatrix[1][0] * vector[0] + this.keyMatrix[1][1] * vector[1]) % this.MOD
            ];
            encrypted.push(...result);
        }

        // Store original length as first character
        const lengthChar = String.fromCharCode(65 + (originalLength % 26));
        return lengthChar + this.numbersToString(encrypted);
    }

    decrypt(ciphertext) {
        const inverseMatrix = HillCipher.matrixInverse(this.keyMatrix, this.MOD);
        if (!inverseMatrix) {
            throw new Error('Key matrix is not invertible');
        }

        // Extract original length from first character
        const lengthChar = ciphertext.charAt(0);
        const originalLength = lengthChar.charCodeAt(0) - 65;
        
        // Remove length character and decrypt the rest
        const actualCiphertext = ciphertext.substring(1);
        const numbers = this.stringToNumbers(actualCiphertext);
        const decrypted = [];

        for (let i = 0; i < numbers.length; i += 2) {
            const vector = [numbers[i], numbers[i + 1]];
            const result = [
                (inverseMatrix[0][0] * vector[0] + inverseMatrix[0][1] * vector[1]) % this.MOD,
                (inverseMatrix[1][0] * vector[0] + inverseMatrix[1][1] * vector[1]) % this.MOD
            ];
            result[0] = (result[0] + this.MOD) % this.MOD;
            result[1] = (result[1] + this.MOD) % this.MOD;
            decrypted.push(...result);
        }

        const fullDecrypted = this.numbersToString(decrypted);
        return fullDecrypted.substring(0, originalLength);
    }
}

// SDES Implementation
class SDES {
    constructor(key) {
        if (key.length !== 10 || !/^[01]+$/.test(key)) {
            throw new Error('Key must be 10 bits (0s and 1s only)');
        }
        this.key = key;
        this.generateSubkeys();
    }

    // S-Boxes
    S0 = [
        [1, 0, 3, 2],
        [3, 2, 1, 0],
        [0, 2, 1, 3],
        [3, 1, 3, 2]
    ];

    S1 = [
        [0, 1, 2, 3],
        [2, 0, 1, 3],
        [3, 0, 1, 0],
        [2, 1, 0, 3]
    ];

    // Permutation tables
    P10 = [2, 4, 1, 6, 3, 9, 0, 8, 7, 5];
    P8 = [5, 2, 6, 3, 7, 4, 9, 8];
    P4 = [1, 3, 2, 0];
    IP = [1, 5, 2, 0, 3, 7, 4, 6];
    IP_INV = [3, 0, 2, 4, 6, 1, 7, 5];
    EP = [3, 0, 1, 2, 1, 2, 3, 0];

    permute(input, table) {
        return table.map(pos => input[pos]).join('');
    }

    leftShift(bits, positions) {
        return bits.substring(positions) + bits.substring(0, positions);
    }

    generateSubkeys() {
        const p10Result = this.permute(this.key, this.P10);
        
        let left = p10Result.substring(0, 5);
        let right = p10Result.substring(5, 10);
        
        left = this.leftShift(left, 1);
        right = this.leftShift(right, 1);
        this.k1 = this.permute(left + right, this.P8);
        
        left = this.leftShift(left, 2);
        right = this.leftShift(right, 2);
        this.k2 = this.permute(left + right, this.P8);
    }

    xor(a, b) {
        return a.split('').map((bit, i) => 
            (parseInt(bit) ^ parseInt(b[i])).toString()
        ).join('');
    }

    fFunction(right, subkey) {
        const expanded = this.permute(right, this.EP);
        const xored = this.xor(expanded, subkey);
        
        const left4 = xored.substring(0, 4);
        const right4 = xored.substring(4, 8);
        
        const s0Row = parseInt(left4[0] + left4[3], 2);
        const s0Col = parseInt(left4[1] + left4[2], 2);
        const s0Out = this.S0[s0Row][s0Col].toString(2).padStart(2, '0');
        
        const s1Row = parseInt(right4[0] + right4[3], 2);
        const s1Col = parseInt(right4[1] + right4[2], 2);
        const s1Out = this.S1[s1Row][s1Col].toString(2).padStart(2, '0');
        
        return this.permute(s0Out + s1Out, this.P4);
    }

    encrypt(plaintext) {
        if (plaintext.length !== 8 || !/^[01]+$/.test(plaintext)) {
            throw new Error('Plaintext must be 8 bits');
        }

        let current = this.permute(plaintext, this.IP);
        let left = current.substring(0, 4);
        let right = current.substring(4, 8);
        
        const fResult1 = this.fFunction(right, this.k1);
        const newLeft = this.xor(left, fResult1);
        
        const fResult2 = this.fFunction(newLeft, this.k2);
        const finalRight = this.xor(right, fResult2);
        
        return this.permute(finalRight + newLeft, this.IP_INV);
    }

    decrypt(ciphertext) {
        if (ciphertext.length !== 8 || !/^[01]+$/.test(ciphertext)) {
            throw new Error('Ciphertext must be 8 bits');
        }

        let current = this.permute(ciphertext, this.IP);
        let left = current.substring(0, 4);
        let right = current.substring(4, 8);
        
        const fResult1 = this.fFunction(right, this.k2);
        const newLeft = this.xor(left, fResult1);
        
        const fResult2 = this.fFunction(newLeft, this.k1);
        const finalRight = this.xor(right, fResult2);
        
        return this.permute(finalRight + newLeft, this.IP_INV);
    }

    encryptText(text) {
        const binaryText = text.split('').map(char => 
            char.charCodeAt(0).toString(2).padStart(8, '0')
        ).join('');

        const blocks = binaryText.match(/.{1,8}/g) || [];
        return blocks.map(block => this.encrypt(block)).join('');
    }

    decryptText(cipherBinary) {
        const blocks = cipherBinary.match(/.{1,8}/g) || [];
        const decryptedBinary = blocks.map(block => this.decrypt(block)).join('');
        
        const bytes = decryptedBinary.match(/.{1,8}/g) || [];
        return bytes.map(byte => String.fromCharCode(parseInt(byte, 2))).join('');
    }
}

// LSB Steganography Implementation
class LSBSteganography {
    static hideMessage(imageData, message) {
        const binaryMessage = this.stringToBinary(message) + '1111111111111110'; // End marker
        const pixels = imageData.data;
        
        if (binaryMessage.length > pixels.length) {
            throw new Error('Message too long for image capacity');
        }

        const newImageData = new ImageData(
            new Uint8ClampedArray(pixels),
            imageData.width,
            imageData.height
        );

        for (let i = 0; i < binaryMessage.length; i++) {
            const bit = parseInt(binaryMessage[i]);
            newImageData.data[i] = (pixels[i] & 0xFE) | bit;
        }

        return newImageData;
    }

    static extractMessage(imageData) {
        const pixels = imageData.data;
        const endMarker = '1111111111111110';
        let binaryMessage = '';

        for (let i = 0; i < pixels.length; i++) {
            const bit = pixels[i] & 1;
            binaryMessage += bit.toString();
            
            if (binaryMessage.endsWith(endMarker)) {
                binaryMessage = binaryMessage.slice(0, -endMarker.length);
                break;
            }
        }

        return this.binaryToString(binaryMessage);
    }

    static stringToBinary(text) {
        return text.split('').map(char => 
            char.charCodeAt(0).toString(2).padStart(8, '0')
        ).join('');
    }

    static binaryToString(binary) {
        const bytes = binary.match(/.{1,8}/g) || [];
        return bytes.map(byte => String.fromCharCode(parseInt(byte, 2))).join('');
    }

    static getCapacity(width, height) {
        return Math.floor((width * height * 4) / 8) - 2;
    }
}

// Utility functions
function updateStatus(stepId, status, text) {
    const statusElement = document.getElementById(stepId);
    const textElement = statusElement.querySelector('.status-text');
    
    statusElement.className = 'step-status';
    textElement.className = 'status-text';
    
    if (status === 'complete') {
        textElement.className += ' status-complete';
        textElement.textContent = '✓ ' + text;
    } else if (status === 'processing') {
        textElement.className += ' status-processing';
        textElement.innerHTML = '<span class="loading"></span> ' + text;
    } else {
        textElement.textContent = text;
    }
}

function showResult(elementId, content, isError = false) {
    const element = document.getElementById(elementId);
    element.innerHTML = content;
    if (isError) {
        element.className = 'result error';
    } else {
        element.className = 'result';
    }
}

// Encryption functions
function processHillCipher() {
    const plainText = document.getElementById('plainText').value.trim();
    
    if (!plainText) {
        showResult('hillResult', 'Please enter plain text first', true);
        return;
    }

    const keyMatrix = [
        [parseInt(document.getElementById('key00').value), parseInt(document.getElementById('key01').value)],
        [parseInt(document.getElementById('key10').value), parseInt(document.getElementById('key11').value)]
    ];

    if (!HillCipher.validateKey(keyMatrix)) {
        showResult('hillResult', 'Invalid key matrix. Determinant must be coprime with 26.', true);
        return;
    }

    updateStatus('step2-status', 'processing', 'Encrypting...');
    
    setTimeout(() => {
        try {
            const hillCipher = new HillCipher(keyMatrix);
            const encrypted = hillCipher.encrypt(plainText);
            
            encryptionState.plainText = plainText;
            encryptionState.hillEncrypted = encrypted;
            
            showResult('hillResult', `<strong>Encrypted:</strong> ${encrypted}`);
            updateStatus('step2-status', 'complete', 'Complete');
            updateStatus('step1-status', 'complete', 'Complete');
        } catch (error) {
            showResult('hillResult', `Error: ${error.message}`, true);
            updateStatus('step2-status', 'error', 'Failed');
        }
    }, 1000);
}

function processSDES() {
    if (!encryptionState.hillEncrypted) {
        showResult('sdesResult', 'Please encrypt with Hill Cipher first', true);
        return;
    }

    const sdesKey = document.getElementById('sdesKey').value;
    
    if (!/^[01]{10}$/.test(sdesKey)) {
        showResult('sdesResult', 'SDES key must be exactly 10 bits (0s and 1s)', true);
        return;
    }

    updateStatus('step3-status', 'processing', 'Encrypting...');
    
    setTimeout(() => {
        try {
            const sdes = new SDES(sdesKey);
            const encrypted = sdes.encryptText(encryptionState.hillEncrypted);
            
            encryptionState.sdesEncrypted = encrypted;
            
            showResult('sdesResult', `<strong>Binary Encrypted:</strong> ${encrypted.substring(0, 50)}${encrypted.length > 50 ? '...' : ''}`);
            updateStatus('step3-status', 'complete', 'Complete');
        } catch (error) {
            showResult('sdesResult', `Error: ${error.message}`, true);
            updateStatus('step3-status', 'error', 'Failed');
        }
    }, 1000);
}

function handleImageUpload(input) {
    const file = input.files[0];
    if (!file) return;

    const canvas = document.getElementById('imagePreview');
    const ctx = canvas.getContext('2d');
    const img = new Image();

    img.onload = function() {
        canvas.width = Math.min(img.width, 400);
        canvas.height = Math.min(img.height, 300);
        ctx.drawImage(img, 0, 0, canvas.width, canvas.height);
        canvas.style.display = 'block';
        
        encryptionState.coverImageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
        updateStatus('step4-status', 'complete', 'Complete');
    };

    img.src = URL.createObjectURL(file);
}

function processStego() {
    if (!encryptionState.sdesEncrypted || !encryptionState.coverImageData) {
        showResult('stegoResult', 'Please complete SDES encryption and upload a cover image first', true);
        return;
    }

    updateStatus('step5-status', 'processing', 'Hiding message...');
    
    setTimeout(() => {
        try {
            const stegoImageData = LSBSteganography.hideMessage(
                encryptionState.coverImageData, 
                encryptionState.sdesEncrypted
            );
            
            const canvas = document.getElementById('stegoResult');
            const ctx = canvas.getContext('2d');
            canvas.width = stegoImageData.width;
            canvas.height = stegoImageData.height;
            ctx.putImageData(stegoImageData, 0, 0);
            canvas.style.display = 'block';
            
            encryptionState.stegoImageData = stegoImageData;
            document.getElementById('downloadSection').style.display = 'block';
            updateStatus('step5-status', 'complete', 'Complete');
        } catch (error) {
            showResult('stegoResult', `Error: ${error.message}`, true);
            updateStatus('step5-status', 'error', 'Failed');
        }
    }, 1500);
}

function downloadImage() {
    if (!encryptionState.stegoImageData) return;
    
    const canvas = document.getElementById('stegoResult');
    canvas.toBlob(function(blob) {
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = 'encrypted_image.png';
        a.click();
        URL.revokeObjectURL(url);
    });
}

// Decryption functions
function handleEncryptedImageUpload(input) {
    const file = input.files[0];
    if (!file) return;

    const canvas = document.getElementById('encryptedImagePreview');
    const ctx = canvas.getContext('2d');
    const img = new Image();

    img.onload = function() {
        canvas.width = Math.min(img.width, 400);
        canvas.height = Math.min(img.height, 300);
        ctx.drawImage(img, 0, 0, canvas.width, canvas.height);
        canvas.style.display = 'block';
        
        encryptionState.encryptedImageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
        updateStatus('decrypt-step1-status', 'complete', 'Complete');
    };

    img.src = URL.createObjectURL(file);
}

function extractMessage() {
    if (!encryptionState.encryptedImageData) {
        showResult('extractResult', 'Please upload an encrypted image first', true);
        return;
    }

    updateStatus('decrypt-step2-status', 'processing', 'Extracting...');
    
    setTimeout(() => {
        try {
            const extracted = LSBSteganography.extractMessage(encryptionState.encryptedImageData);
            encryptionState.extractedMessage = extracted;
            
            showResult('extractResult', `<strong>Extracted binary:</strong> ${extracted.substring(0, 50)}${extracted.length > 50 ? '...' : ''}`);
            updateStatus('decrypt-step2-status', 'complete', 'Complete');
        } catch (error) {
            showResult('extractResult', `Error: ${error.message}`, true);
            updateStatus('decrypt-step2-status', 'error', 'Failed');
        }
    }, 1000);
}

function decryptSDES() {
    if (!encryptionState.extractedMessage) {
        showResult('sdesDecryptResult', 'Please extract message from image first', true);
        return;
    }

    const sdesKey = document.getElementById('decryptSdesKey').value;
    
    if (!/^[01]{10}$/.test(sdesKey)) {
        showResult('sdesDecryptResult', 'SDES key must be exactly 10 bits (0s and 1s)', true);
        return;
    }

    updateStatus('decrypt-step3-status', 'processing', 'Decrypting...');
    
    setTimeout(() => {
        try {
            const sdes = new SDES(sdesKey);
            const decrypted = sdes.decryptText(encryptionState.extractedMessage);
            
            encryptionState.sdesDecrypted = decrypted;
            
            showResult('sdesDecryptResult', `<strong>SDES Decrypted:</strong> ${decrypted}`);
            updateStatus('decrypt-step3-status', 'complete', 'Complete');
        } catch (error) {
            showResult('sdesDecryptResult', `Error: ${error.message}`, true);
            updateStatus('decrypt-step3-status', 'error', 'Failed');
        }
    }, 1000);
}

function decryptHillCipher() {
    if (!encryptionState.sdesDecrypted) {
        showResult('hillDecryptResult', 'Please decrypt SDES first', true);
        return;
    }

    const keyMatrix = [
        [parseInt(document.getElementById('decryptKey00').value), parseInt(document.getElementById('decryptKey01').value)],
        [parseInt(document.getElementById('decryptKey10').value), parseInt(document.getElementById('decryptKey11').value)]
    ];

    if (!HillCipher.validateKey(keyMatrix)) {
        showResult('hillDecryptResult', 'Invalid key matrix. Determinant must be coprime with 26.', true);
        return;
    }

    updateStatus('decrypt-step4-status', 'processing', 'Decrypting...');
    
    setTimeout(() => {
        try {
            const hillCipher = new HillCipher(keyMatrix);
            const decrypted = hillCipher.decrypt(encryptionState.sdesDecrypted);
            
            encryptionState.finalDecrypted = decrypted;
            
            showResult('hillDecryptResult', `<strong>Hill Decrypted:</strong> ${decrypted}`);
            updateStatus('decrypt-step4-status', 'complete', 'Complete');
            updateStatus('decrypt-step5-status', 'complete', 'Complete');
            
            // Show final result
            document.getElementById('finalResult').innerHTML = `
                <h4>Original Message Recovered!</h4>
                <p style="font-size: 1.2rem; margin-top: 10px;">"${decrypted}"</p>
            `;
        } catch (error) {
            showResult('hillDecryptResult', `Error: ${error.message}`, true);
            updateStatus('decrypt-step4-status', 'error', 'Failed');
        }
    }, 1000);
}

// Initialize the application
document.addEventListener('DOMContentLoaded', function() {
    console.log('Hybrid Cryptography System loaded successfully!');
    
    // Set default values to sync decrypt keys with encrypt keys
    document.getElementById('key00').addEventListener('input', function() {
        document.getElementById('decryptKey00').value = this.value;
    });
    document.getElementById('key01').addEventListener('input', function() {
        document.getElementById('decryptKey01').value = this.value;
    });
    document.getElementById('key10').addEventListener('input', function() {
        document.getElementById('decryptKey10').value = this.value;
    });
    document.getElementById('key11').addEventListener('input', function() {
        document.getElementById('decryptKey11').value = this.value;
    });
    
    document.getElementById('sdesKey').addEventListener('input', function() {
        document.getElementById('decryptSdesKey').value = this.value;
    });
});
