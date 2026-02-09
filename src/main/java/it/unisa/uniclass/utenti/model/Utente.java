package it.unisa.uniclass.utenti.model;


import jakarta.persistence.Access;
import jakarta.persistence.AccessType;
import jakarta.persistence.MappedSuperclass;

import java.io.Serializable;
import java.time.LocalDate;

/**
 * Classe base per rappresentare un utente generico del sistema.
 * Questa classe è mappata come superclasse per l'uso con JPA.
 * Implementa l'interfaccia Serializable per consentire la serializzazione.
 * */
@MappedSuperclass
@Access(AccessType.FIELD)
public class Utente implements Serializable {

    /**
     * Nome dell'utente
     */
    //@ spec_public
    //@ nullable
    protected String nome;

    /**
     * Cognome dell'utente
     */
    //@ spec_public
    //@ nullable
    protected String cognome;

    /**
     * Data di nascita dell'utente
     */
    //@ spec_public
    //@ nullable
    protected LocalDate dataNascita;

    /**
     * Indirizzo email dell'utente
     */
    //@ spec_public
    //@ nullable
    protected String email;

    /**
     * Password dell'utente
     */
    //@ spec_public
    //@ nullable
    protected String password;

    /**
     * Tipo di utente
     */
    //@ spec_public
    //@ nullable
    protected Tipo tipo;

    /**
     * Numero di telefono del membro del personale TA
     * */
    //@ spec_public
    //@ nullable
    private String telefono;

    /**
     * Data di iscrizione dell'accademico.
     */
    //@ spec_public
    //@ nullable
    protected LocalDate iscrizione;


    /**
     * Costruttore di default.
     * Inizializza un'istanza vuota di Utente.
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures true;
      @*/
    public Utente() {}

    /**
     * Restituisce il nome dell'Utente
     *
     * @return il nome dell'utente
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == nome;
      @*/
    public /*@ nullable */ String getNome() {
        return nome;
    }

    /**
     * Imposta il nome dell'utente.
     *
     * @param nome il nuovo nome dell'utente
     * */
    /*@
      @ public normal_behavior
      @ assignable this.nome;
      @ ensures this.nome == nome;
      @*/
    public void setNome(String nome) {
        this.nome = nome;
    }

    /**
     * Restituisce il cognome dell'utente.
     *
     * @return il cognome dell'utente
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == cognome;
      @*/
    public /*@ nullable */ String getCognome() {
        return cognome;
    }

    /**
     * Imposta il cognome dell'utente.
     *
     * @param cognome il nuovo cognome dell'utente
     * */
    /*@
      @ public normal_behavior
      @ assignable this.cognome;
      @ ensures this.cognome == cognome;
      @*/
    public void setCognome(String cognome) {
        this.cognome = cognome;
    }


    /**
     * Restituisce la data di iscrizione dell'accademico.
     *
     * @return la data di iscrizione, come {@link LocalDate}
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == iscrizione;
      @*/
    public /*@ nullable */ LocalDate getIscrizione() {
        return iscrizione;
    }

    /**
     Imposta la data di iscrizione dell'accademico
     @param iscrizione la nuova data di iscrizione
     @throws IllegalArgumentException se la data è futura.
     */
    /*@
      @ public normal_behavior
      @ assignable this.iscrizione;
      @ ensures this.iscrizione == iscrizione;
      @*/
    public void setIscrizione(LocalDate iscrizione) {
        this.iscrizione = iscrizione;
    }

    /**
     * Restituisce la data di nascita dell'utente
     *
     * @return la data di nascita dell'Utente
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == dataNascita;
      @*/
    public /*@ nullable */ LocalDate getDataNascita() {
        return dataNascita;
    }

    /**
     * Imposta la data di nascita dell'utente.
     *
     * @param dataNascita la nuova data di nascita dell'utente
     * */
    /*@
      @ public normal_behavior
      @ assignable this.dataNascita;
      @ ensures this.dataNascita == dataNascita;
      @*/
    public void setDataNascita(LocalDate dataNascita) {
        this.dataNascita = dataNascita;
    }

    /**
     * Restituisce l'indirizzo email dell'utente.
     *
     * @return l'email dell'utente
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == email;
      @*/
    public /*@ nullable */ String getEmail() {
        return email;
    }

    /**
     * Imposta l'indirizzo email dell'utente
     *
     * @param email il nuovo indirizzo email dell'utente
     * */
    /*@
      @ public normal_behavior
      @ assignable this.email;
      @ ensures this.email == email;
      @*/
    public void setEmail(String email) {
        this.email = email;
    }


    /**
     * Restituisce il numero di telefono del membro del personale TA
     *
     * @return Il numero di telefono del membro del personale TA.
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == telefono;
      @*/
    public /*@ nullable */ String getTelefono() {
        return telefono;
    }

    /**
     * Imposta il numero di telefono del membro del personale TA
     *
     * @param telefono Il numero di telefono del membro del personale TA.
     * */
    /*@
      @ public normal_behavior
      @ assignable this.telefono;
      @ ensures this.telefono == telefono;
      @*/
    public void setTelefono(String telefono) {
        this.telefono = telefono;
    }

    /**
     * Restituisce la password dell'utente
     *
     * @return la password dell'utente
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == password;
      @*/
    public /*@ nullable */ String getPassword() {
        return password;
    }

    /**
     * Imposta la password dell'utente.
     *
     * @param password la nuova password dell'utente
     * */
    /*@
      @ public normal_behavior
      @ assignable this.password;
      @ ensures this.password == password;
      @*/
    public void setPassword(String password) {
        this.password = password;
    }

    /**
     * Restituisce il tipo di utente
     *
     * @return il tipo di utente
     * */
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == tipo;
      @*/
    public /*@ nullable */ Tipo getTipo() {
        return tipo;
    }

    /**
     * Imposta il tipo di utente.
     *
     * @param tipo il nuovo tipo di utente
     * */
    /*@
      @ public normal_behavior
      @ assignable this.tipo;
      @ ensures this.tipo == tipo;
      @*/
    public void setTipo(Tipo tipo) {
        this.tipo = tipo;
    }

    /**
     * Restituisce una rappresentazione in formato stringa dell'oggetto Utente.
     *
     * @return una stringa contenente le informazioni dell'Utente
     * */
    //@ skipesc
    @Override
    public String toString() {
        return "Utente{" +
                "nome='" + nome + '\'' +
                ", cognome='" + cognome + '\'' +
                ", dataNascita=" + dataNascita +
                ", email='" + email + '\'' +
                ", password='" + password + '\'' +
                '}';
    }
}
