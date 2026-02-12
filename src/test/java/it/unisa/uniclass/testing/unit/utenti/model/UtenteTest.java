package it.unisa.uniclass.testing.unit.utenti.model;

import it.unisa.uniclass.utenti.model.Tipo;
import it.unisa.uniclass.utenti.model.Utente;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test unitario per la classe Utente.
 */
class UtenteTest {

    @Test
    @DisplayName("Test del Costruttore Vuoto e dei Setter/Getter")
    void testNoArgsConstructorAndSetters() {
        // 1. Istanziazione con costruttore vuoto (copre "public Utente() {}")
        Utente utente = new Utente();

        // Dati di test
        String email = "test@unisa.it";
        String password = "passwordSegreta123";
        String nome = "Mario";
        String cognome = "Rossi";
        LocalDate dataNascita = LocalDate.of(1995, 5, 20);
        String telefono = "3331234567";
        LocalDate iscrizione = LocalDate.now();

        Tipo tipo = Tipo.Accademico;

        // 2. Esecuzione dei Setter
        utente.setEmail(email);
        utente.setPassword(password);
        utente.setNome(nome);
        utente.setCognome(cognome);
        utente.setDataNascita(dataNascita);
        utente.setTelefono(telefono);
        utente.setIscrizione(iscrizione);
        utente.setTipo(tipo);

        // 3. Verifica con i Getter (copre le linee "return x")
        assertAll("Verifica proprietà Utente impostate via Setter",
                () -> assertEquals(email, utente.getEmail(), "L'email non corrisponde"),
                () -> assertEquals(password, utente.getPassword(), "La password non corrisponde"),
                () -> assertEquals(nome, utente.getNome(), "Il nome non corrisponde"),
                () -> assertEquals(cognome, utente.getCognome(), "Il cognome non corrisponde"),
                () -> assertEquals(dataNascita, utente.getDataNascita(), "La data di nascita non corrisponde"),
                () -> assertEquals(telefono, utente.getTelefono(), "Il telefono non corrisponde"),
                () -> assertEquals(iscrizione, utente.getIscrizione(), "La data di iscrizione non corrisponde"),
                () -> assertEquals(tipo, utente.getTipo(), "Il tipo non corrisponde")
        );
    }

    @Test
    @DisplayName("Test del Costruttore con Parametri")
    void testAllArgsConstructor() {
        // Dati di test
        String email = "luigi.verdi@unisa.it";
        String password = "securePass!@#";
        String nome = "Luigi";
        String cognome = "Verdi";
        LocalDate dataNascita = LocalDate.of(1980, 10, 12);
        String telefono = "3339876543";
        LocalDate iscrizione = LocalDate.of(2023, 9, 1);

        Tipo tipo = Tipo.PersonaleTA;

        // 1. Istanziazione con costruttore completo (copre l'assegnazione diretta)
        Utente utente = new Utente(email, password, nome, cognome, dataNascita, telefono, iscrizione, tipo);

        // 2. Verifica immediata
        assertAll("Verifica proprietà Utente istanziate via Costruttore",
                () -> assertEquals(email, utente.getEmail()),
                () -> assertEquals(password, utente.getPassword()),
                () -> assertEquals(nome, utente.getNome()),
                () -> assertEquals(cognome, utente.getCognome()),
                () -> assertEquals(dataNascita, utente.getDataNascita()),
                () -> assertEquals(telefono, utente.getTelefono()),
                () -> assertEquals(iscrizione, utente.getIscrizione()),
                () -> assertEquals(tipo, utente.getTipo())
        );
    }
}