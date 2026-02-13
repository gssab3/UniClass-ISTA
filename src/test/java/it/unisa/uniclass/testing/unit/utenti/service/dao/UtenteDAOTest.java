package it.unisa.uniclass.testing.unit.utenti.service.dao;


import it.unisa.uniclass.utenti.model.*;
import it.unisa.uniclass.utenti.service.dao.UtenteDAO;
import jakarta.persistence.EntityManager;
import jakarta.persistence.NoResultException;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class UtenteDAOTest {

    private void inject(Object target, String field, Object value) throws Exception {
        Field f = target.getClass().getDeclaredField(field);
        f.setAccessible(true);
        f.set(target, value);
    }

    @Test
    void delete_shouldMergeThenRemove_whenNotContained() throws Exception {
        UtenteDAO dao = new UtenteDAO();
        EntityManager em = mock(EntityManager.class);
        Utente u = new Utente();
        Utente merged = new Utente();

        when(em.contains(u)).thenReturn(false);
        when(em.merge(u)).thenReturn(merged);

        inject(dao, "em", em);

        dao.delete(u);

        verify(em).merge(u);
        verify(em).remove(merged);
    }

    @Test
    void delete_shouldRemoveDirectly_whenContained() throws Exception {
        UtenteDAO dao = new UtenteDAO();
        EntityManager em = mock(EntityManager.class);
        Utente u = new Utente();

        when(em.contains(u)).thenReturn(true);

        inject(dao, "em", em);

        dao.delete(u);

        verify(em, never()).merge(any());
        verify(em).remove(u);
    }

    @Test
    void findByEmail_shouldReturnUser_whenFound() throws Exception {
        UtenteDAO dao = new UtenteDAO();
        EntityManager em = mock(EntityManager.class);
        TypedQuery<Utente> q = mock(TypedQuery.class);
        Utente u = new Utente();

        when(em.createNamedQuery("Utente.findByEmail", Utente.class)).thenReturn(q);
        when(q.setParameter("email", "a@b.it")).thenReturn(q);
        when(q.getSingleResult()).thenReturn(u);

        inject(dao, "em", em);

        assertEquals(u, dao.findByEmail("a@b.it"));
    }

    @Test
    void findByEmail_shouldReturnNull_whenNotFound() throws Exception {
        UtenteDAO dao = new UtenteDAO();
        EntityManager em = mock(EntityManager.class);
        TypedQuery<Utente> q = mock(TypedQuery.class);

        when(em.createNamedQuery("Utente.findByEmail", Utente.class)).thenReturn(q);
        when(q.setParameter("email", "x")).thenReturn(q);
        when(q.getSingleResult()).thenThrow(new NoResultException());

        inject(dao, "em", em);

        assertNull(dao.findByEmail("x"));
    }

    @Test
    void existsByEmail_shouldReturnTrue_whenCountGreaterThanZero() throws Exception {
        UtenteDAO dao = new UtenteDAO();
        EntityManager em = mock(EntityManager.class);
        TypedQuery<Long> q = mock(TypedQuery.class);

        when(em.createNamedQuery("Utente.checkExists", Long.class)).thenReturn(q);
        when(q.setParameter("email", "a")).thenReturn(q);
        when(q.getSingleResult()).thenReturn(5L);

        inject(dao, "em", em);

        assertTrue(dao.existsByEmail("a"));
    }

    @Test
    void existsByEmail_shouldReturnFalse_whenCountIsZero() throws Exception {
        UtenteDAO dao = new UtenteDAO();
        EntityManager em = mock(EntityManager.class);
        TypedQuery<Long> q = mock(TypedQuery.class);

        when(em.createNamedQuery("Utente.checkExists", Long.class)).thenReturn(q);
        when(q.setParameter("email", "a")).thenReturn(q);
        when(q.getSingleResult()).thenReturn(0L);

        inject(dao, "em", em);

        assertFalse(dao.existsByEmail("a"));
    }

    @Test
    void findByTipo_shouldReturnList() throws Exception {
        UtenteDAO dao = new UtenteDAO();

        // Mock EntityManager e TypedQuery
        EntityManager em = mock(EntityManager.class);
        TypedQuery<Utente> q = mock(TypedQuery.class);

        // Stub createQuery con qualsiasi stringa
        when(em.createQuery(anyString(), eq(Utente.class))).thenReturn(q);
        when(q.setParameter(anyString(), any())).thenReturn(q);

        // Lista simulata
        when(q.getResultList()).thenReturn(List.of(new Utente()));

        // Iniezione EntityManager
        Field f = UtenteDAO.class.getDeclaredField("em");
        f.setAccessible(true);
        f.set(dao, em);

        // Test
        assertEquals(1, dao.findByTipo("DOCENTE").size());

        // Verifica che setParameter sia chiamato correttamente
        verify(q).setParameter("tipo", "DOCENTE");
    }

}
