#! D:\крипта\venv\Scripts\python.exe
# Объявление использования интерпретатора Python3

import collections
import hashlib
import random
from flask import Flask, request, jsonify

app = Flask(__name__)
EllipticCurve = collections.namedtuple('EllipticCurve', 'name p a b g n h')

"Параметры кривой (Как у Эфириума :) )"

"Простое p, задающее размер конечного поля."
"Коэффициенты a и b уравнения эллиптической кривой."
"Базовая точка G, генерирующая подгруппу."
"Порядок n подгруппы."
"Кофактор подгруппы."

curve = EllipticCurve(
    'secp256k1', 
    p=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f,
    a=0,
    b=7,
    g=(0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
       0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8),
    n=0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141,
    h=1,
)

"Расширенный алгоритм Евклида для нахождения обратной k по mod(p)"
def inverse_mod(k, p):
    if k == 0:
        raise ZeroDivisionError('Деление на ноль')

    if k < 0:
        return p - inverse_mod(-k, p)

    s, old_s = 0, 1
    t, old_t = 1, 0
    r, old_r = p, k

    while r != 0:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t

    gcd, x, y = old_r, old_s, old_t

    assert gcd == 1
    assert (k * x ) % p == 1

    return x % p

"Проверка принадлжености точки к кривой"
def is_on_curve(point):
    if point is None:
        return True

    x, y = point

    return (y * y - x * x * x - curve.a * x - curve.b) % curve.p == 0

"Нахождение обратной точки"
def point_neg(point):
    assert is_on_curve(point)
    "Если точка нулевая"
    if point is None:
        return None

    x, y = point
    result = (x, -y % curve.p)

    assert is_on_curve(result)

    return result

"Сложение двух точек"
def point_add(point1, point2):
    assert is_on_curve(point1)
    assert is_on_curve(point2)

    if point1 is None:
        return point2
    if point2 is None:
        return point1

    x1, y1 = point1
    x2, y2 = point2

    "Если у точек равны x, но не равны y, то сложение невозможно"
    if x1 == x2 and y1 != y2:
        return None
    "Если точки равны"
    if x1 == x2:
        m = (3 * x1 * x1 + curve.a) * inverse_mod(2 * y1, curve.p)
    else:
        m = (y1 - y2) * inverse_mod(x1 - x2, curve.p)

    "Формула нахождения 3-ей точки"
    x3 = m * m - x1 - x2
    y3 = y1 + m * (x3 - x1)
    result = (x3 % curve.p,
              -y3 % curve.p)

    assert is_on_curve(result)

    return result

"Алгоритм сложения-умножения улючей, представляющий собой упрощенный способ сложения точки k раз"
"Если бит k == 1, то мы складываем (2P+P), а затем увеличиваем степень 2(2^2P+2P+P)"
"Либо если бит == 0, то просто увеличиваем степень"
def scalar_mult(k, point):
    assert is_on_curve(point)

    if k % curve.n == 0 or point is None:
        return None

    if k < 0:
        return scalar_mult(-k, point_neg(point))

    result = None
    addend = point
    
    while k:
        if k & 1:
            result = point_add(result, addend)
        addend = point_add(addend, addend)

        k >>= 1

    assert is_on_curve(result)

    return result

"Создание приватного(подбором от 1 до n) и публичного(алгоритм умножения-сложения) ключей"
def make_keypair():
    private_key = random.randrange(1, curve.n)
    public_key = scalar_mult(private_key, curve.g)

    return private_key, public_key

"Хэширование сообщения алгоритмом sha512 и усечение преобразованного сообщения до длины"
"Порядка группы n"
def hash_message(message):
    message_hash = hashlib.sha512(message).digest()
    e = int.from_bytes(message_hash, 'big')
    z = e >> (e.bit_length() - curve.n.bit_length())
    assert z.bit_length() <= curve.n.bit_length()

    return z

"Подпись сообщение путём хэширования сообщения, подбора скаляра k, вычисления новой точки"
"Вычисления чисел r и s болших, чем 0, по фромулам. r и s будут являться подписью "
def sign_message(private_key, message):
    z = hash_message(message)

    r = 0
    s = 0

    while not r or not s:
        k = random.randrange(1, curve.n)
        x, y = scalar_mult(k, curve.g)

        r = x % curve.n 
        s = ((z + r * private_key) * inverse_mod(k, curve.n)) % curve.n

    return (r, s)

"Проверка подписи путём хэширования сообщения, нахождения обратной s по модулю n"
"Нахождение 2-х целых чисел u1 u2, вычисление новой точки (На самом деле той же,"
"что была на втором шаге вычисления подписи)"
def verify_signature(public_key, message, signature):
    z = hash_message(message)

    r, s = signature

    inversed_s = inverse_mod(s, curve.n)
    u1 = (z * inversed_s) % curve.n
    u2 = (r * inversed_s) % curve.n

    x, y = point_add(scalar_mult(u1, curve.g),
                     scalar_mult(u2, public_key))

    if (r % curve.n) == (x % curve.n):
        return 'подпись верна'
    else:
        return 'ошибка подписи'


@app.route('/sign', methods=['POST'])
def sign():
    message = request.json['message']
    private_key, public_key = make_keypair()
    signature = sign_message(private_key, message.encode())
    return jsonify({
        'message_and_signature': message+"#"+str(signature[0])+"#"+str(signature[1]),
        'pub': public_key
    })

@app.route('/verify', methods=['POST'])
def verify():
    data = request.json
    
    message_and_signature = data['message_and_signature']
    message = message_and_signature.split('#')[0]
    signature = int(message_and_signature.split('#')[1]),int(message_and_signature.split('#')[2])
    
    public_key = data['public_key']
    result = verify_signature(public_key, message.encode(), signature)
    return jsonify({'verification_result': result})

if __name__ == '__main__':
    app.run(debug=True)