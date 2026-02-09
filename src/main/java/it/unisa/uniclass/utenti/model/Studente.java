package it.unisa.uniclass.utenti.model;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import jakarta.persistence.*;

import java.io.Serializable;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

import static it.unisa.uniclass.utenti.model.Studente.*;

/**
 * Classe che rappresenta uno studente nel sistema UniClass.
 * Estende la classe {@link Accademico} e include funzionalità specifiche per gli studenti.
 * Implementa l'interfaccia {@link Serializable} per supportare la serializzazione.
 */
@Entity
@Access(AccessType.FIELD)
@Table(name = "studenti")
@NamedQueries({
        @NamedQuery(name = "Studente.trovaStudente", query = "SELECT s FROM Studente s WHERE s.matricola = :matricola"),
        @NamedQuery(name = "Studente.trovaPerCorso", query = "SELECT s FROM Studente s WHERE s.corsoLaurea.nome = :nome"),
        @NamedQuery(name = "Studente.trovaTutti", query = "SELECT s FROM Studente s"),
        @NamedQuery(name = "Studente.trovaEmail", query = "SELECT s FROM Studente s WHERE s.email = :email")
})
public class Studente extends Accademico implements Serializable {

    /**
     * Nome della query per trovare uno studente tramite la matricola.
     */
    public static final String TROVA_STUDENTE = "Studente.trovaStudente";
    /**
     * Nome della query per trovare tutti gli studenti di un determinato corso di laurea.
     */
    public static final String TROVA_STUDENTI_CORSO = "Studente.trovaPerCorso";
    /**
     * Nome della queryy per trovare tutti gli studenti
     * */
    public static final String TROVA_TUTTI = "Studente.trovaTutti";
    /**
     * Nome della query per trovare uno strudente tramite l'email.
     * */
    public static final String TROVA_EMAIL = "Studente.trovaEmail";


    /**
     * Costruttore predefinito.
     * Inizializza le liste e setta il tipo a {@link Tipo#Studente}.
     * */
    //@ skipesc
    public Studente() {
        super.setTipo(Tipo.Studente);
    }


   

    /**
     * Costruttore con parametri.
     * Inizializza i campi principali dello stuedente.
     * */
    //@ skipesc
    public Studente(String nome, String cognome, LocalDate dataNascita, String email, String password, String matricola, LocalDate iscrizione, CorsoLaurea corsoLaurea, Resto resto) {
        super.setNome(nome);
        super.setCognome(cognome);
        super.setEmail(email);
        super.setCorsoLaurea(corsoLaurea);
        super.setDataNascita(dataNascita);
        super.setIscrizione(iscrizione);
        super.setPassword(password);
        super.setTipo(Tipo.Studente);
        super.setMatricola(matricola);
        this.resto = resto;
        super.setCorsoLaurea(corsoLaurea); //modifica per (java:S2387)
    }

    /**
     * Restituisce il resto associato allo studente
     *
     * @return Oggetto {@link Resto}.
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == resto;
      @*/
    public /*@ nullable */ Resto getResto() {
        return resto;
    }

    /**
     * Imposta il resto associato allo Studente.
     *
     * @param resto Oggetto {@link Resto} da associare.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.resto;
      @ ensures this.resto == resto;
      @*/
    public void setResto(Resto resto) {
        this.resto = resto;
    }

    /**
     * Restituisce una rappresentazione in formato stringa dell'oggetto Studente.
     *
     * @return Stringa rappresentativa dello studente.
     * */
    //@ skipesc
    @Override
    public String toString() {
        return "Studente{" +
                "nome='" + nome + '\'' +
                ", cognome='" + cognome + '\'' +
                ", dataNascita=" + dataNascita +
                ", email='" + email + '\'' +
                ", tipo=" + tipo +
                ", matricola='" + matricola + '\'' +
                ", iscrizione=" + iscrizione +
                ", corsoLaurea=" + getCorsoLaurea() +
                '}';
    }
}
