import setuptools


setuptools.setup(name='tshash',
                 version='1.0.0',
                 description='TSHash Implementation',
                 long_description=open('README.md').read().strip(),
                 author='Itay Bookstein',
                 py_modules=['tshash'],
                 install_requires=['bitstring'],
                 license='MIT License',
                 zip_safe=False,
                 keywords='tshash')
